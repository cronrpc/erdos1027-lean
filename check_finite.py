"""Exact finite checks for the Erdos 1027 partial-colouring argument.

No third-party dependencies. These checks are not a proof of the asymptotic
theorem. They test the joint-colour probability, uniform completion, and
representative-extension counting for every 3-uniform hypergraph on 5 vertices.
"""
from fractions import Fraction
from itertools import combinations, product
import json


def main():
    vertex_count = 5
    all_bits = (1 << vertex_count) - 1
    partials = []
    for states in product(range(3), repeat=vertex_count):
        gray = sum(1 << v for v, s in enumerate(states) if s == 0)
        red = sum(1 << v for v, s in enumerate(states) if s == 1)
        blue = all_bits ^ (gray | red)
        completion_mask = sum(
            1 << coloring
            for coloring in range(1 << vertex_count)
            if coloring & red == red and coloring & blue == 0
        )
        partials.append((red, blue, gray, gray.bit_count(), completion_mask))

    # p = 1/3: every partial state has probability 3^(-vertex_count).
    uniform_mass = []
    for coloring in range(1 << vertex_count):
        mass = sum(
            (Fraction(1, 3 ** vertex_count * 2 ** g)
             for _, _, _, g, mask in partials if mask >> coloring & 1),
            Fraction(0),
        )
        assert mass == Fraction(1, 1 << vertex_count)
        uniform_mass.append(str(mass))

    pair_checks = 0
    self_pair_checks = 0
    p = Fraction(1, 3)
    a = Fraction(2, 3)
    for n in range(1, vertex_count + 1):
        edges = [sum(1 << v for v in edge)
                 for edge in combinations(range(vertex_count), n)]
        for edge_a in edges:
            for edge_b in edges:
                ell = (edge_a & edge_b).bit_count()
                observed = Fraction(sum(
                    (edge_a & red == 0 and edge_b & blue == 0)
                    for red, blue, _, _, _ in partials
                ), 3 ** vertex_count)
                predicted = p ** ell * a ** (2 * (n - ell))
                assert observed == predicted
                if ell:
                    assert predicted <= p * a ** (2 * n - 2)
                pair_checks += 1
                self_pair_checks += edge_a == edge_b

    edges = [sum(1 << v for v in edge)
             for edge in combinations(range(vertex_count), 3)]
    good_partial_checks = 0
    partial_checks = 0
    total_families = 1 << len(edges)
    for family_code in range(total_families):
        family = [edge for i, edge in enumerate(edges) if family_code >> i & 1]
        proper_mask = sum(
            1 << coloring for coloring in range(1 << vertex_count)
            if all((coloring & edge) not in (0, edge) for edge in family)
        )
        weighted_success_sum = 0
        for red, blue, gray, g, completions in partials:
            successes = (proper_mask & completions).bit_count()
            weighted_success_sum += successes * 2 ** (vertex_count - g)
            need_red = [edge for edge in family if edge & red == 0]
            need_blue = [edge for edge in family if edge & blue == 0]
            constraints = len(need_red) + len(need_blue)
            empty_constraint = any(edge & gray == 0
                                   for edge in need_red + need_blue)
            # Deliberately includes the self pair, excluding all-gray edges.
            opposite_conflict = any(ar & ab for ar in need_red for ab in need_blue)
            partial_checks += 1
            if empty_constraint or opposite_conflict:
                continue

            forced_red = 0
            forced_blue = 0
            for edge in need_red:
                available = edge & gray
                forced_red |= available & -available
            for edge in need_blue:
                available = edge & gray
                forced_blue |= available & -available
            assert forced_red & forced_blue == 0
            fixed = (forced_red | forced_blue).bit_count()
            assert fixed <= constraints
            forced_completions = sum(
                1 << coloring for coloring in range(1 << vertex_count)
                if completions >> coloring & 1
                and coloring & forced_red == forced_red
                and coloring & forced_blue == 0
            )
            assert forced_completions & proper_mask == forced_completions
            assert forced_completions.bit_count() == 2 ** (g - fixed)
            assert successes * 2 ** constraints >= 2 ** g
            good_partial_checks += 1

        # Exact mixture probability agrees with direct uniform enumeration.
        assert weighted_success_sum == proper_mask.bit_count() * 3 ** vertex_count

    print(json.dumps({
        "status": "all exact checks passed",
        "method": "exhaustive enumeration with integer/Fraction arithmetic",
        "universe_vertices": vertex_count,
        "uniform_hyperedge_size": 3,
        "families_checked": total_families,
        "partial_coloring_checks": partial_checks,
        "good_partial_extension_checks": good_partial_checks,
        "ordered_pair_probability_checks": pair_checks,
        "included_self_pairs": self_pair_checks,
        "each_final_coloring_probability": uniform_mass[0],
        "scope_limit": "finite sanity checks, not a proof for all n and c",
    }, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
