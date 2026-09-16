import Std

/-!
A dependency-light formalization of the compatible representative lemma.
There is no finiteness assumption and no counting assertion in this file.
Each nonempty constraint requests one Boolean colour.  Opposite requests
have disjoint available sets, so chosen representatives can all be coloured
consistently.  Every colouring extending those choices meets the requests.
-/

namespace Erdos1027Core

theorem compatible_completion {α I : Type}
    (S : I → α → Prop) (b : I → Bool)
    (hne : ∀ i, ∃ v, S i v)
    (hcompat : ∀ i j, b i ≠ b j → ∀ v, S i v → S j v → False) :
    ∃ (r : I → α) (f : α → Bool),
      (∀ i, S i (r i)) ∧
      (∀ i, f (r i) = b i) ∧
      (∀ g : α → Bool, (∀ i, g (r i) = f (r i)) →
        ∀ i, ∃ v, S i v ∧ g v = b i) := by
  classical
  let r : I → α := fun i => Classical.choose (hne i)
  have hr (i : I) : S i (r i) := Classical.choose_spec (hne i)
  let f : α → Bool := fun v =>
    if h : ∃ i, r i = v then b (Classical.choose h) else false
  have hrep (i : I) : f (r i) = b i := by
    have hex : ∃ j, r j = r i := ⟨i, rfl⟩
    simp only [f, dif_pos hex]
    apply Classical.byContradiction
    intro hc
    have hj : r (Classical.choose hex) = r i := Classical.choose_spec hex
    exact hcompat (Classical.choose hex) i hc (r (Classical.choose hex))
      (hr (Classical.choose hex)) (by simpa only [hj] using hr i)
  refine ⟨r, f, hr, hrep, ?_⟩
  intro g hg i
  refine ⟨r i, hr i, ?_⟩
  rw [hg i, hrep i]

/-- In particular, a colouring satisfying all requests exists. -/
theorem compatible_completion_exists {α I : Type}
    (S : I → α → Prop) (b : I → Bool)
    (hne : ∀ i, ∃ v, S i v)
    (hcompat : ∀ i j, b i ≠ b j → ∀ v, S i v → S j v → False) :
    ∃ f : α → Bool, ∀ i, ∃ v, S i v ∧ f v = b i := by
  obtain ⟨r, f, hr, hf, _⟩ := compatible_completion S b hne hcompat
  exact ⟨f, fun i => ⟨r i, hr i, hf i⟩⟩

end Erdos1027Core

#print axioms Erdos1027Core.compatible_completion
#print axioms Erdos1027Core.compatible_completion_exists
