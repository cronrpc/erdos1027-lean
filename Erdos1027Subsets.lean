import Erdos1027Completion

/-! Exact correspondence between proper Boolean colourings and splitting
subsets, so that the final result can be stated in the original set language. -/
noncomputable section
open Classical

namespace Erdos1027Subsets

variable {V : Type*} [Fintype V] [DecidableEq V]

def Splits (F : Finset (Finset V)) (B : Finset V) : Prop :=
  ∀ A ∈ F, (A ∩ B).Nonempty ∧ (A \ B).Nonempty

def redSet (g : V → Bool) : Finset V := Finset.univ.filter fun v => g v = true

def colorOfSet (B : Finset V) : V → Bool := fun v => decide (v ∈ B)

theorem proper_redSet (F : Finset (Finset V)) (g : V → Bool)
    (hg : Erdos1027.Proper F g) : Splits F (redSet g) := by
  intro A hA
  obtain ⟨v, hv, hvtrue⟩ := hg A hA true
  obtain ⟨w, hw, hwfalse⟩ := hg A hA false
  constructor
  · exact ⟨v, Finset.mem_inter.mpr ⟨hv, by simp [redSet, hvtrue]⟩⟩
  · exact ⟨w, Finset.mem_sdiff.mpr ⟨hw, by simp [redSet, hwfalse]⟩⟩

theorem splits_colorOfSet (F : Finset (Finset V)) (B : Finset V)
    (hB : Splits F B) : Erdos1027.Proper F (colorOfSet B) := by
  intro A hA b
  obtain ⟨⟨v, hv⟩, ⟨w, hw⟩⟩ := hB A hA
  have hv' := Finset.mem_inter.mp hv
  have hw' := Finset.mem_sdiff.mp hw
  cases b with
  | false => exact ⟨w, hw'.1, by simp [colorOfSet, hw'.2]⟩
  | true => exact ⟨v, hv'.1, by simp [colorOfSet, hv'.2]⟩

def properEquivSplits (F : Finset (Finset V)) :
    {g : V → Bool // Erdos1027.Proper F g} ≃ {B : Finset V // Splits F B} where
  toFun g := ⟨redSet g.val, proper_redSet F g.val g.property⟩
  invFun B := ⟨colorOfSet B.val, splits_colorOfSet F B.val B.property⟩
  left_inv g := by
    apply Subtype.ext
    funext v
    cases h : g.val v <;> simp [colorOfSet, redSet, h]
  right_inv B := by
    apply Subtype.ext
    ext v
    simp [redSet, colorOfSet]

theorem proper_card_eq_splitting_card (F : Finset (Finset V)) :
    Nat.card {g : V → Bool // Erdos1027.Proper F g} =
      Nat.card {B : Finset V // Splits F B} :=
  Nat.card_congr (properEquivSplits F)

end Erdos1027Subsets
