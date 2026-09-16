import Mathlib.Data.Fintype.BigOperators
import Mathlib.SetTheory.Cardinal.Finite

/-!
# The finite completion lemma for Erdős problem 1027

Each constraint specifies a nonempty finite set of available vertices and a
requested Boolean colour.  Sets with opposite requests are disjoint.  Choosing
one representative for each constraint therefore fixes at most one vertex per
constraint, without conflicting requests.  Every extension of these choices
satisfies every constraint.
-/

namespace Erdos1027

/-- A colouring meets each of the requested colour constraints. -/
def Meets {α I : Type*} (S : I → Finset α) (b : I → Bool) (g : α → Bool) : Prop :=
  ∀ i, ∃ v ∈ S i, g v = b i

/-- Compatible nonempty constraints admit a certificate fixing at most one
vertex per constraint.  Every extension of the certificate meets all requests. -/
theorem completion_certificate {α I : Type*} [Fintype I]
    (S : I → Finset α) (b : I → Bool)
    (hne : ∀ i, (S i).Nonempty)
    (hcompat : ∀ i j, b i ≠ b j → Disjoint (S i) (S j)) :
    ∃ (T : Finset α) (f : α → Bool),
      T.card ≤ Fintype.card I ∧
      ∀ g : α → Bool, (∀ v ∈ T, g v = f v) → Meets S b g := by
  classical
  let r : I → α := fun i => Classical.choose (hne i)
  have hr (i : I) : r i ∈ S i := Classical.choose_spec (hne i)
  let T : Finset α := Finset.univ.image r
  let f : α → Bool := fun v =>
    if h : ∃ i, r i = v then b (Classical.choose h) else false
  have hrep (i : I) : f (r i) = b i := by
    have hex : ∃ j, r j = r i := ⟨i, rfl⟩
    simp only [f, dif_pos hex]
    apply Classical.byContradiction
    intro hc
    have hj := Classical.choose_spec hex
    have hd := Finset.disjoint_left.mp (hcompat (Classical.choose hex) i hc)
    exact hd (hr (Classical.choose hex)) (by simpa [hj] using hr i)
  refine ⟨T, f, ?_, ?_⟩
  · exact (Finset.card_image_le).trans (by simp)
  · intro g hg i
    refine ⟨r i, hr i, ?_⟩
    rw [hg (r i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩), hrep]

/-- A Boolean colouring on the complement of a fixed certificate extends to
the entire vertex set, preserving the certificate. -/
noncomputable def extend {α : Type*} (T : Finset α) (f : α → Bool)
    (u : {v : α // v ∉ T} → Bool) : α → Bool := by
  classical
  exact fun v => if h : v ∈ T then f v else u ⟨v, h⟩

theorem extend_agrees {α : Type*} (T : Finset α) (f : α → Bool)
    (u : {v : α // v ∉ T} → Bool) :
    ∀ v ∈ T, extend T f u v = f v := by
  classical
  intro v hv
  simp [extend, hv]

theorem extend_injective {α : Type*} (T : Finset α) (f : α → Bool) :
    Function.Injective (extend T f) := by
  classical
  intro u w h
  funext v
  have he := congrFun h v.val
  simpa [extend, v.property] using he

/-- Fixing a certificate on `T` leaves exactly `|α| - |T|` freely coloured
vertices, yielding at least that many powers of two in any extension-closed
property. -/
theorem card_of_certificate {α : Type*} [Fintype α]
    (P : (α → Bool) → Prop) (T : Finset α) (f : α → Bool)
    (hP : ∀ g, (∀ v ∈ T, g v = f v) → P g) :
    2 ^ (Fintype.card α - T.card) ≤ Nat.card {g : α → Bool // P g} := by
  classical
  let Φ : ({v : α // v ∉ T} → Bool) → {g : α → Bool // P g} :=
    fun u => ⟨extend T f u, hP _ (extend_agrees T f u)⟩
  have hΦ : Function.Injective Φ := by
    intro u w h
    exact extend_injective T f (congrArg Subtype.val h)
  have hcard := Fintype.card_le_of_injective Φ hΦ
  simpa [Nat.card_eq_fintype_card, Fintype.card_fun,
    Fintype.card_subtype_compl, Fintype.card_coe] using hcard

/-- Quantitative completion: each compatible constraint costs at most one
binary degree of freedom.  No bound on the number of constraints is needed;
the natural-number subtraction makes the bound equal to one when `|I| ≥ |α|`.
-/
theorem completion_count {α I : Type*} [Fintype α] [Fintype I]
    (S : I → Finset α) (b : I → Bool)
    (hne : ∀ i, (S i).Nonempty)
    (hcompat : ∀ i j, b i ≠ b j → Disjoint (S i) (S j)) :
    2 ^ (Fintype.card α - Fintype.card I) ≤
      Nat.card {g : α → Bool // Meets S b g} := by
  obtain ⟨T, f, hT, hP⟩ := completion_certificate S b hne hcompat
  apply le_trans _ (card_of_certificate (Meets S b) T f hP)
  exact Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_left hT _)

/-- An equivalent convenient multiplicative lower bound, without truncated
subtraction. -/
theorem completion_count_mul {α I : Type*} [Fintype α] [Fintype I]
    (S : I → Finset α) (b : I → Bool)
    (hne : ∀ i, (S i).Nonempty)
    (hcompat : ∀ i j, b i ≠ b j → Disjoint (S i) (S j)) :
    2 ^ Fintype.card α ≤
      Nat.card {g : α → Bool // Meets S b g} * 2 ^ Fintype.card I := by
  classical
  obtain ⟨T, f, hT, hP⟩ := completion_certificate S b hne hcompat
  calc
    2 ^ Fintype.card α =
        2 ^ (Fintype.card α - T.card) * 2 ^ T.card := by
      rw [← pow_add, Nat.sub_add_cancel (Finset.card_le_univ T)]
    _ ≤ Nat.card {g : α → Bool // Meets S b g} * 2 ^ Fintype.card I :=
      Nat.mul_le_mul (card_of_certificate (Meets S b) T f hP)
        (Nat.pow_le_pow_right (by decide) hT)

/-- Fill grey vertices from a Boolean seed; already fixed colours are kept. -/
def complete {V : Type*} (c : V → Option Bool) (u : V → Bool) : V → Bool :=
  fun v => (c v).getD (u v)

/-- Every edge contains a vertex of each colour. -/
def Proper {V : Type*} (F : Finset (Finset V)) (u : V → Bool) : Prop :=
  ∀ A ∈ F, ∀ b : Bool, ∃ v ∈ A, u v = b

/-- Edges with no vertex already fixed to the requested colour. -/
noncomputable def requests {V : Type*} (F : Finset (Finset V))
    (c : V → Option Bool) (b : Bool) : Finset (Finset V) := by
  classical
  exact F.filter fun A => ∀ v ∈ A, c v ≠ some b

@[simp] theorem mem_requests {V : Type*} (F : Finset (Finset V))
    (c : V → Option Bool) (b : Bool) (A : Finset V) :
    A ∈ requests F c b ↔ A ∈ F ∧ ∀ v ∈ A, c v ≠ some b := by
  classical
  exact Finset.mem_filter

/-- For a good partial colouring, at least a `2⁻ᴸ` fraction of all Boolean
seeds give a proper completed colouring.  Sampling the seed on all vertices
avoids a variable probability space: seed bits at already fixed vertices are
simply ignored by `complete`.
-/
theorem good_partial_seed_count {V : Type*} [Fintype V]
    (F : Finset (Finset V)) (c : V → Option Bool) (L : ℕ)
    (hgray : ∀ b A, A ∈ requests F c b → ∃ v ∈ A, c v = none)
    (hdisjoint : ∀ A ∈ requests F c true, ∀ B ∈ requests F c false,
      Disjoint A B)
    (hM : (requests F c true).card + (requests F c false).card ≤ L) :
    2 ^ Fintype.card V ≤
      Nat.card {u : V → Bool // Proper F (complete c u)} * 2 ^ L := by
  classical
  let I := (↥(requests F c true)) ⊕ (↥(requests F c false))
  let S : I → Finset V := Sum.elim
    (fun A => A.val.filter fun v => c v = none)
    (fun A => A.val.filter fun v => c v = none)
  let b : I → Bool := Sum.elim (fun _ => true) (fun _ => false)
  have hne : ∀ i, (S i).Nonempty := by
    intro i
    cases i with
    | inl A =>
      obtain ⟨v, hv, hg⟩ := hgray true A.val A.property
      exact ⟨v, Finset.mem_filter.mpr ⟨hv, hg⟩⟩
    | inr A =>
      obtain ⟨v, hv, hg⟩ := hgray false A.val A.property
      exact ⟨v, Finset.mem_filter.mpr ⟨hv, hg⟩⟩
  have hcompat : ∀ i j, b i ≠ b j → Disjoint (S i) (S j) := by
    intro i j hij
    cases i with
    | inl A =>
      cases j with
      | inl B => exact False.elim (hij rfl)
      | inr B =>
        apply Finset.disjoint_left.mpr
        intro v hv hw
        exact Finset.disjoint_left.mp
          (hdisjoint A.val A.property B.val B.property)
          (Finset.mem_filter.mp hv).1 (Finset.mem_filter.mp hw).1
    | inr A =>
      cases j with
      | inl B =>
        apply Finset.disjoint_left.mpr
        intro v hv hw
        exact Finset.disjoint_left.mp
          (hdisjoint B.val B.property A.val A.property)
          (Finset.mem_filter.mp hw).1 (Finset.mem_filter.mp hv).1
      | inr B => exact False.elim (hij rfl)
  have hvalid (u : V → Bool) (hu : Meets S b u) : Proper F (complete c u) := by
    intro A hA color
    by_cases hreq : A ∈ requests F c color
    · cases color with
      | false =>
        obtain ⟨v, hv, hcol⟩ := hu (Sum.inr ⟨A, hreq⟩)
        obtain ⟨hvA, hgv⟩ := Finset.mem_filter.mp hv
        exact ⟨v, hvA, by simpa [complete, hgv, b] using hcol⟩
      | true =>
        obtain ⟨v, hv, hcol⟩ := hu (Sum.inl ⟨A, hreq⟩)
        obtain ⟨hvA, hgv⟩ := Finset.mem_filter.mp hv
        exact ⟨v, hvA, by simpa [complete, hgv, b] using hcol⟩
    · have hfixed : ∃ v ∈ A, c v = some color := by
        apply Classical.byContradiction
        intro h
        apply hreq
        rw [mem_requests]
        refine ⟨hA, ?_⟩
        intro v hv hc
        exact h ⟨v, hv, hc⟩
      obtain ⟨v, hv, hc⟩ := hfixed
      exact ⟨v, hv, by simp [complete, hc]⟩
  have hcard : Nat.card {u : V → Bool // Meets S b u} ≤
      Nat.card {u : V → Bool // Proper F (complete c u)} := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Fintype.card_le_of_injective
      (fun u => (⟨u.val, hvalid u.val u.property⟩ :
        {u : V → Bool // Proper F (complete c u)}))
      (by
        intro u w h
        apply Subtype.ext
        exact congrArg
          (fun z : {u : V → Bool // Proper F (complete c u)} => z.val) h)
  have hI : Fintype.card I ≤ L := by
    simpa only [I, Fintype.card_sum, Fintype.card_coe] using hM
  exact (completion_count_mul S b hne hcompat).trans
    (Nat.mul_le_mul hcard (Nat.pow_le_pow_right (by decide) hI))

end Erdos1027

#print axioms Erdos1027.completion_count_mul
#print axioms Erdos1027.good_partial_seed_count
