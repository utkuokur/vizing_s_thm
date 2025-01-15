import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Tactic.LibrarySearch
import Mathlib.Data.Fintype.Basic

variable {V : Type} [Fintype V] [CompleteLinearOrder V]

def eq_class (r: V → V → Prop) : V → Set V := fun a => { x | r a x }

def f_compare (r: V → V → Prop)
 : V → V := fun a => sInf (eq_class r a)

lemma f_respects (r: V → V → Prop) (h : Equivalence r): ∀ a b, r a b → f_compare r a = f_compare r b := by
intros a b h₁
apply le_antisymm
· apply sInf_le_sInf
  intros x hx
  unfold eq_class at hx
  have hbx : r b x := by exact hx
  unfold eq_class
  have h₃ : r a x := by exact h.trans h₁ hbx
  exact h₃
· apply sInf_le_sInf
  intros y hy
  unfold eq_class at hy
  have hay : r a y := by exact hy
  unfold eq_class
  have h₄ : r b y := by apply h.symm at h₁; apply h.trans h₁ hay
  exact h₄

lemma lifting_map (r: V → V → Prop) (h : Equivalence r) : (Quot r) → V := Quot.lift (f_compare r) (f_respects r h)

def induced_LE : (Set V) → (Set V) → Prop :=  fun a => fun b => (sInf a) ≤ (sInf b)

def induced_quot_LE (r: V → V → Prop)  (h : Equivalence r) : (Quot r) → (Quot r) → Prop := fun x => fun y => lifting_map r h x ≤ lifting_map r h y

instance linearOrderInducesLinear (r: V → V → Prop ) : CompleteLinearOrder (Quot r) := sorry

instance induced_complete_linear_prod : CompleteLinearOrder ( V × V ) := by sorry

def induced_Sym2_LE  : (Sym2 V) → (Sym2 V) → Prop := induced_quot_LE (Sym2.Rel V) Sym2.Rel.is_equivalence

instance induced_complete_linear_Sym2 : CompleteLinearOrder ( Sym2 V) := by sorry

lemma Sym2_empty_is_empty : IsEmpty (Sym2 (∅ : Set V ))  := by exact Sym2.instIsEmptySym2
