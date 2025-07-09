--Written by Dr. Matthew Ballard and Utku Okur

import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Walk
import Mathlib.Tactic
import Mathlib.Data.Fintype.Basic

open SimpleGraph Hom Iso Embedding Classical Sym2 Walk List

variable {V : Type} {G : SimpleGraph V} {v : V} {T : Type v}

def closedNbhdSubgraph (v : V) : SimpleGraph {w : V| G.Adj v w ∨ w = v} where
  Adj := fun w₁ w₂ => G.Adj w₁ w₂ ∧ (w₁ = v ∨ w₂ = v)
  symm := by
    intro v₁ v₂ h
    constructor
    · apply G.symm h.left
    · match h.right with
      | .inl h => exact .inr h
      | .inr h => exact .inl h

def AdjacentAt (v : V) (e₁ e₂ : edgeSet G) : Prop := Sym2.Mem v e₁ ∧ Sym2.Mem v e₂

theorem AdjacentAt.symm {v : V} {e₁ e₂ : edgeSet G} (h : AdjacentAt v e₁ e₂) : AdjacentAt v e₂ e₁ := ⟨h.right, h.left⟩

def Adjacent (e₁ e₂ : edgeSet G) : Prop := ∃ v, AdjacentAt v e₁ e₂

lemma Adjacent_symm {e₁ e₂ : edgeSet G} (h : Adjacent e₁ e₂) : Adjacent e₂ e₁ := by
obtain ⟨w,h'⟩ := h
exact ⟨w, AdjacentAt.symm h'⟩

def lineGraph (G : SimpleGraph V) : SimpleGraph (edgeSet G) where
  Adj := fun e₁ e₂ => Adjacent e₁ e₂ ∧ e₁ ≠ e₂
  symm := by intro e₁ e₂ h ; exact ⟨ Adjacent_symm h.1, h.2.symm ⟩

variable (G :  SimpleGraph V) (v : V)

abbrev EdgeColoring (T : Type v) := Coloring (lineGraph G) T

theorem EdgeColoring.valid {T : Type v} {G : SimpleGraph V}
    (c : EdgeColoring G T) {e₁ e₂ : edgeSet G} (h : e₁ ≠ e₂)
    (adj : Adjacent e₁ e₂ ) : c e₁ ≠ c e₂ :=
  Coloring.valid c ⟨adj,h⟩

variable {n:ℕ} {C: EdgeColoring G (Fin n)} {α β : (Fin n)} {h_αβ : α ≠ β }

noncomputable def edgeChromaticNumber : ENat := chromaticNumber (lineGraph G)

open Fintype Finset

def edgeSpan : Set (edgeSet G) := fun e => Sym2.Mem v e

def neighborSettoEdge (v' : neighborSet G v) : Sym2 V := s(v,v')

lemma other_not_eq_given {x y : V} (hne : x ≠ y) (h₁ : x ∈ s(x,y)) : (Sym2.Mem.other h₁) = y := by
  have h : x ∈ s(x, y) :=
      Sym2.mem_iff.mpr <| .inl rfl
  have h' : (Sym2.Mem.other (h)) = x ∨ (Sym2.Mem.other (h)) = y := Sym2.mem_iff.mp (Sym2.other_mem h)
  have h'' : Sym2.Mem.other h ≠ x := by
      have H : s(x, Sym2.Mem.other h) = s(x, y) := Sym2.other_spec h
      have H' : y ∈ s(x, y) := Sym2.mem_mk_right x y
      rw [←H] at H'
      have H'' :  y ∈ s(x, Sym2.Mem.other h) ↔ (y = x ∨ y = Sym2.Mem.other h) := Sym2.mem_iff
      rw [H''] at H'
      cases' H' with w w
      by_contra
      exact hne (Eq.symm w)
      cases' h' with X X
      by_contra
      rw [←X] at hne
      exact hne (_root_.id (Eq.symm w))
      rw [←X] at hne
      exact _root_.id (Ne.symm hne)
  cases' h' with Y Y
  by_contra
  exact h'' Y
  rw [Y]

noncomputable def neighborSetedgeSpanEquiv : (neighborSet G v) ≃ (edgeSpan G v) where
  toFun := fun ⟨v',hv'⟩ => by
    refine ⟨⟨  s(v,v') ,hv'⟩, ?_⟩
    · change v ∈ s(v, ↑v')
      rw [Sym2.mem_iff]
      exact Or.inl rfl
  invFun := fun ⟨⟨e,he⟩,he'⟩ => by
    refine ⟨Sym2.Mem.other he',?_⟩
    dsimp [neighborSet]
    rw [←mem_edgeSet,Sym2.other_spec he']
    exact he
  left_inv := fun ⟨v',hv'⟩ => by
    dsimp
    congr
    apply other_not_eq_given (ne_of_adj G hv')
  right_inv := fun ⟨⟨e,he⟩,he'⟩ => by
    dsimp
    congr
    exact Sym2.other_spec he'

theorem edgeSpan_isClique : IsClique (lineGraph G) <| edgeSpan G v := fun _ he₁ _ he₂ ne => ⟨⟨v,⟨he₁,he₂⟩⟩,ne⟩

lemma reverse_not_nil {V : Type} {G : SimpleGraph V} {u v : V} {p : G.Walk u v}
    :  ¬ p.Nil -> ¬ p.reverse.Nil := by
    intro h₁ h₂
    rw [ Walk.nil_iff_length_eq, Walk.length_reverse ] at *
    exact h₁ h₂

lemma append_not_nil {V : Type} {G : SimpleGraph V} {u v z : V} {p : G.Walk v z}
{r : G.Walk z u} {h_nil : ¬ r.Nil }  : ¬ (p.append r).Nil := by
cases p with
| nil => simpa
| cons => rw [Walk.cons_append ] ; exact Walk.not_nil_cons

lemma concat_not_nil {V : Type} {G : SimpleGraph V} {v u z: V} {h : G.Adj z u}
{p : G.Walk v z} : ¬ (p.concat h).Nil := by simp [Walk.concat] ; apply append_not_nil ; simp

lemma append_snd {V : Type} {G : SimpleGraph V} {u v w : V}
    (p : G.Walk u v) (r : G.Walk v w) (h : ¬ p.Nil) :
    p.snd = (p.append r).snd := by
  cases p with
  | nil =>  simp at *
  | cons =>
    simp [Walk.append, Walk.snd]

theorem append_tail_eq_tail_append {p : G.Walk u v} {r : G.Walk v w} {h_nil : ¬ p.Nil} :
  (p.append r).tail  = Walk.copy (p.tail.append r) (append_snd p r h_nil) rfl  := by
  cases p with
  | nil => simp at h_nil
  | cons _ p' =>
  cases p' with
  | nil => simp
  | cons => simp

--unused so far
lemma cons_reverse_second {V : Type} {G : SimpleGraph V} {v u w: V} {h_adj : G.Adj u v}
{p : G.Walk v w} (h_nil : ¬ p.Nil): p.reverse.snd = (Walk.cons h_adj p).reverse.snd := by
  induction p with
  | nil => simp at *
  | cons _ p' a_ih =>
  repeat rw [ Walk.reverse_cons ]
  cases p' with
  | nil => simp
  | cons _ _ =>
  repeat rw [ <- append_snd ]
  · apply reverse_not_nil ; apply Walk.not_nil_cons
  · rw [ <-Walk.reverse_cons ] ; apply reverse_not_nil ; apply Walk.not_nil_cons ; assumption
  · apply reverse_not_nil ; apply Walk.not_nil_cons

theorem h_second_penult {V : Type} {G : SimpleGraph V} {v u: V}
{ p : G.Walk v u } (h_nil : ¬ p.Nil) : p.penultimate = p.reverse.snd := by
    induction p with
    | nil => simp
    | cons _ p' a_ih =>
    simp [ cons_reverse_second ] at *
    cases p' with
    | nil => simp
    | cons _ _ =>
    rw [Walk.penultimate_cons_of_not_nil]
    · rw [ <- append_snd ]
      · apply a_ih ; apply Walk.not_nil_cons
      · apply reverse_not_nil ; apply Walk.not_nil_cons
    · apply Walk.not_nil_cons

lemma insert_edgeset_non_diag { V : Type } [ Fintype V] [ DecidableEq V] {e : (Sym2 V)}
(h_e_not_diag : ¬ e.IsDiag) {S : Finset (Sym2 V)}
: (fromEdgeSet ((insert e S).toSet)).edgeSet = ((fromEdgeSet S.toSet).edgeSet) ∪ {e}:= by
simp
ext f
constructor
· simp ; intro hS hf ; exact hS.imp_right (And.intro · hf)
· simp ; intro hS; exact ⟨ hS.imp (id) (And.left), hS.elim (· ▸ h_e_not_diag) And.right⟩
--unused so far

-- s(x,y) ≠ f and same color implies contradiction
lemma same_color_helper {V : Type} {G : SimpleGraph V} {n : ℕ} {C: EdgeColoring G (Fin n)}
{ x y: V } {h_adj : G.Adj x y} (f: edgeSet G) {h_x : x ∉ (f: Sym2 V)} { h_y : y ∈ ( f: Sym2 V )}
(h_diff : C ⟨ s(x,y), h_adj ⟩  = C f)
: False:= by
apply Coloring.valid at h_diff
assumption
simp [lineGraph ]
constructor
· simp [Adjacent]
  use y
  simp [AdjacentAt]
  assumption
· by_contra h₂
  rw [<-h₂] at h_x
  simp at h_x

-- if x is adjacent to distinct y₁ and y₂, then C colors the edges xy₁ and xy₂ differently
lemma same_color_impossible {V : Type} {G : SimpleGraph V} {n : ℕ} {C: EdgeColoring G (Fin n)}
{ x y₁ y₂ : V } (h₁ : G.Adj y₁ x) (h₂ : G.Adj y₂ x) (h_neq : y₁ ≠ y₂)
(h_diff : C ⟨ s(y₁,x), (mem_edgeSet G).mp h₁ ⟩ = C ( ⟨ s(y₂,x), (mem_edgeSet G).mp h₂ ⟩ )) : False := by
apply same_color_helper ⟨ s(y₂,x), (mem_edgeSet G).mp h₂ ⟩ h_diff
simp
exact ⟨h_neq, (G.ne_of_adj h₁) ⟩
simp

inductive at_prop {V : Type} {G : SimpleGraph V} {n:ℕ} {C : EdgeColoring G (Fin n)} { α β : Fin n }
  : ∀ { u v : V }, G.Walk u v → Prop where
  | nil : ∀ {v : V}, at_prop (Walk.nil' v)
  | ba : ∀ {u₂ u₁ v : V}, (p : G.Walk u₁ v) -> (h_prev : @at_prop V G n C α β u₁ v p)
   -> (h_adj : G.Adj u₂ u₁) -> C ⟨ s(u₂, u₁), by rw [mem_edgeSet]; exact h_adj ⟩  = α
   -> (h_norepeat : u₂ ∉ p.support) -> at_prop (Walk.cons h_adj p)
  | ab : ∀ {u₂ u₁ v : V}, (p : G.Walk u₁ v) -> (h_prev : @at_prop V G n C α β u₁ v p )
  -> (h_adj : G.Adj u₂ u₁) -> {hp : ¬ p.Nil } -> C ⟨ s(u₂, u₁), by rw [mem_edgeSet]; exact h_adj ⟩  = β
  -> (h_norepeat : u₂ ∉ p.support) -> at_prop (Walk.cons h_adj p)

lemma at_prop_path {V : Type} {G : SimpleGraph V} {n:ℕ} {C : EdgeColoring G (Fin n)} { α β : Fin n }
{v u: V} {p : G.Walk v u} {h_at_prop: @at_prop _ _ _ C α β _ _ p } :
p.IsPath := by
induction h_at_prop with
  | nil => exact Walk.IsPath.nil
  | ba _ _ _  _ h_norepeat ih =>
    exact Walk.IsPath.cons ih h_norepeat
  | ab _ _ _ _ h_norepeat ih =>
    exact Walk.IsPath.cons ih h_norepeat

lemma at_prop_outsider {v u t s: V} {h_sv: s ≠ v ∧ s ≠ u }  {p: G.Walk v u}
{h_st: G.Adj t s} {n: ℕ} {C: EdgeColoring G (Fin n)} {α β : (Fin n)}
{h_prop : @at_prop _ _ _ C α β v u p} {hs_sup: s ∈ p.support} {ht_sup: t ∉ p.support}
{h_color: C ⟨ s(t,s), h_st ⟩ ∈ [α,β]} : False := by
induction h_prop with
| nil => simp at * ; contradiction
| @ab a b c p' h_prev h_adj h_nil h_c_ab h_rep a_ih =>
simp at *
rcases h_sv with ⟨ h₁, h₂ ⟩
simp [h₁] at hs_sup
have h_sb : s ≠ b := by
  intro h_sb
  simp [h_sb] at h_color h_st
  cases h_color with
  |inl h₁ =>
    cases h_prev with
    |nil => simp at *
    | @ab a' b' c' p'' _ h_adj' _ h_color =>
      simp at *
      have h_ab' : a ≠ b' := by
        intro h_ab'
        simp [ h_ab'] at h_rep
      have h₃ : C ⟨s(b',b), h_adj'.symm ⟩ = β := by simp [Sym2.eq_swap] ; exact h_color
      rw [<- h₃ ] at h_c_ab
      exact same_color_impossible h_adj h_adj'.symm h_ab' h_c_ab
    | @ba a' b' c' p'' _ h_adj' h_color _ =>
      have h_tb' : t ≠ b' := by intro h_tb' ; simp [h_tb'] at ht_sup
      have h₃ : C ⟨s(b',b), h_adj'.symm ⟩ = α := by simp [Sym2.eq_swap] ; exact h_color
      simp [<- h₃ ] at h₁
      exact same_color_impossible h_st h_adj'.symm h_tb' h₁
  |inr h₂ =>
    rw [<-h_c_ab] at h₂
    exact same_color_impossible h_st h_adj ht_sup.1 h₂
specialize a_ih h_sb h₂
exact hs_sup
exact ht_sup.2 a_ih

| @ba a b c p' h_prev h_adj h_c_ab h_rep a_ih =>
simp at *
rcases h_sv with ⟨ h₁, h₂ ⟩
simp [h₁] at hs_sup
have h_sb : s ≠ b := by
  intro h_sb
  simp [h_sb] at h_color h_st
  cases h_color with
  |inl h₁ =>
    rw [<-h_c_ab] at h₁
    exact same_color_impossible h_st h_adj ht_sup.1 h₁
  |inr h₂ =>
    cases h_prev with
    |nil => contradiction
    | @ab a' b' c' p'' _ h_adj' _ h_color =>
      simp at *
      have h_tb' : t ≠ b' := by intro h_tb' ; simp [h_tb'] at ht_sup
      have h₃ : C ⟨s(b',b), h_adj'.symm ⟩ = β := by simp [Sym2.eq_swap] ; exact h_color
      rw [<- h₃ ] at h₂
      exact same_color_impossible h_st h_adj'.symm  h_tb' h₂
    | @ba a' b' c' p'' _ h_adj' h_color _ =>
      have h_ab' : a ≠ b' := by
        intro h_ab'
        simp [ h_ab'] at h_rep
      have h₃ : C ⟨s(b',b), h_adj'.symm ⟩ = α := by simp [Sym2.eq_swap] ; exact h_color
      rw [<- h₃ ] at h_c_ab
      exact same_color_impossible h_adj  h_adj'.symm h_ab' h_c_ab
specialize a_ih h_sb h₂
exact hs_sup
exact ht_sup.2 a_ih

lemma adj_of_edge {V : Type} {G : SimpleGraph V} {ℓ₁ ℓ₂: V} {f: edgeSet G}
(h_ed : s(ℓ₂,ℓ₁) = (f: Sym2 V)) : G.Adj ℓ₂ ℓ₁  := by apply (mem_edgeSet G).mp ; rw [h_ed] ; simp

lemma lift_edge_type {V : Type} {G : SimpleGraph V} {f₁ f₂ : ( edgeSet G )}
{h_diff: f₁ ≠ f₂} : (f₁ : Sym2 V) ≠ (f₂ : Sym2 V) := by intro h' ; exact h_diff (Subtype.coe_inj.mp h' )

class edge_used {V : Type} {G : SimpleGraph V} {n: ℕ} {C: EdgeColoring G (Fin n)}
{α β : Fin n} {v ℓ₁ ℓ₂: V} {p : G.Walk ℓ₁ v} {f: edgeSet G} : Prop where
h_ed : s(ℓ₂,ℓ₁) = (f: Sym2 V)
alt_prop: @at_prop _ _ _ C α β ℓ₂ v (Walk.cons (adj_of_edge h_ed) p)

def R_ed_y : edgeSet G → Prop := fun f => ∃ (ℓ₁ ℓ₂ : V), ∃ (p: G.Walk ℓ₁ v), @edge_used V G n C α β v ℓ₁ ℓ₂ p f

lemma extend_reachable_αβ {V : Type} {G : SimpleGraph V} {n: ℕ} {C: EdgeColoring G (Fin n)} {v ℓ₁ ℓ₂ : V}
(α β : (Fin n)) (f₁ f₂ : ( edgeSet G )) (h_adj : (lineGraph G).Adj f₁ f₂) {p : G.Walk ℓ₁ v}
(h_δv: v ∉ (f₂:Sym2 V)) (f₁_reachable: @edge_used V G n C α β v ℓ₁ ℓ₂ p f₁)
( h_color₁ : C f₁ = α ) ( h_color₂ : C f₂ = β ) (h_ab: α ≠ β)
: ∃ (ℓ₁' ℓ₂' : V), ∃ (p': G.Walk ℓ₁' v), @edge_used V G n C α β v ℓ₁' ℓ₂' p' f₂
∧ p'.support ⊆ (insert ℓ₂ p.support)
:= by
obtain ⟨h_ed, h_at_p ⟩ := f₁_reachable
simp [ lineGraph, Adjacent, AdjacentAt ] at h_adj
rcases h_adj with ⟨ h₁ , h₂ ⟩
obtain ⟨ z, hz⟩ := h₁
rcases hz with ⟨ hzf₁ , hzf₂ ⟩
rw [<-h_ed] at hzf₁
let other := Sym2.Mem.other hzf₂
have h_of₂ : other ∈ (f₂: (Sym2 V)) := by apply Sym2.other_mem
have h_zo: other ≠ z := by simp only [other] ; apply Sym2.other_ne ; apply not_isDiag_of_mem_edgeSet G ; simp
have h_ed₂ : f₂ = s(other, z) := (Sym2.mem_and_mem_iff h_zo).mp ⟨ h_of₂, hzf₂ ⟩
have h₃ : z = ℓ₂ ∨ z = ℓ₁ :=  Sym2.mem_iff'.mp hzf₁
cases h₃ with
|inl hzℓ₁ => --extending the alternating path by appending f₂
rw [hzℓ₁] at hzf₁

use ℓ₂, other, (Walk.cons (adj_of_edge h_ed) p)
have h_f₂_ed : s(other, ℓ₂) = f₂ := by simp [Sym2.eq_swap, other, <- hzℓ₁ ]
constructor
· refine { h_ed := ?_, alt_prop := ?_ }
  · exact h_f₂_ed
  · apply at_prop.ab
    exact h_at_p
    repeat simp [h_f₂_ed]
    exact h_color₂
    simp
    constructor
    · exact G.ne_of_adj (adj_of_edge h_f₂_ed)
    · intro h_sup
      have h_oℓ₁ : other ≠ ℓ₁ := by
        intro h_oℓ₁
        rw [<-h_oℓ₁, Sym2.eq_swap, h_f₂_ed ] at h_ed
        have h_diff_sym2 : (f₁ : Sym2 V) ≠ (f₂ : Sym2 V):= @lift_edge_type V G f₁ f₂ h₂
        exact h_diff_sym2.symm h_ed
      have h_ov : other ≠ v := by
        intro h_ov
        have h_vf₂ : v ∈ (f₂ : Sym2 V) := by
          rw [<- h_ov]
          exact h_of₂
        contradiction

      simp [Sym2.eq_swap] at h_f₂_ed
      cases h_at_p with
      |ab _ h_prev _ _  =>
      apply @at_prop_outsider V G ℓ₁ v ℓ₂ other ⟨ h_oℓ₁, h_ov ⟩ p (adj_of_edge h_f₂_ed)  n C α β h_prev h_sup
      assumption
      simp [h_f₂_ed]
      exact Or.inr h_color₂
      |ba _ h_prev _ _  =>
      apply @at_prop_outsider V G ℓ₁ v ℓ₂ other ⟨ h_oℓ₁, h_ov ⟩ p (adj_of_edge h_f₂_ed)  n C α β h_prev h_sup
      assumption
      simp [h_f₂_ed]
      exact Or.inr h_color₂
· simp [insert]
  exact List.subset_insert ℓ₂ p.support
  |inr hzℓ₂ => --f₂ is already on the path
    rw [hzℓ₂] at h_ed₂
    cases h_at_p with
    | ba _  h_prev₁ h_adj₁ h_col₁ h_rep =>
      cases h_prev₁ with
      |nil =>
        have h_vf₂ : v ∈ (f₂ : Sym2 V) := by
          rw [<-hzℓ₂]
          exact hzf₂
        contradiction
      | @ba a b c h_rep _ h_adj₂ h_col₂ =>
      have h₃ : C ⟨s(b,ℓ₁), h_adj₂.symm ⟩ = α := by simp [Sym2.eq_swap] ; exact h_col₂
      have h_bℓ₂ : ℓ₂ ≠ b := by intro h ; simp [h] at h_rep
      rw [<- h₃ ] at h_col₁
      by_contra
      exact same_color_impossible h_adj₁ h_adj₂.symm h_bℓ₂ h_col₁
      | @ab a b c p₂ h_prev₂ h_adj₂ h_nil h_col₂ =>
        have h₃ : C ⟨s(b,ℓ₁), h_adj₂.symm ⟩ = β := by simp [Sym2.eq_swap] ; exact h_col₂
        have h₄ : C ⟨s(other,ℓ₁), (adj_of_edge h_ed₂.symm) ⟩ = β := by simp [<- h_ed₂] ; assumption
        have h_ob : other = b := by
          by_contra h_ob
          rw [<-h₃] at h₄
          exact same_color_impossible (adj_of_edge h_ed₂.symm) h_adj₂.symm  h_ob h₄
        subst h_ob
        use other, ℓ₁, p₂
        constructor
        · refine { h_ed := ?_, alt_prop := ?_ } ;
          · rw [Sym2.eq_swap] ; exact h_ed₂.symm
          · apply at_prop.ab ; repeat assumption
        · simp [insert] ; intro a h ; simp ; exact Or.inr (Or.inr h) ;
    | ab _ _  _ h_col =>
      simp [h_ed] at h_col
      rw [h_col] at h_color₁
      rw [<-h_color₁] at h_ab
      contradiction

def walk_terminal_tail {V : Type} {G : SimpleGraph V} {v u : V} (p : G.Walk v u)
: G.Walk v p.reverse.snd := p.reverse.tail.reverse

lemma copy_at_prop {V : Type} {G : SimpleGraph V} {v u v' u': V} {n:ℕ} {C : EdgeColoring G (Fin n)}
{ α β : Fin n} { p : G.Walk v u } { h₁ : v = v' } { h₂ : u = u' } :
 @at_prop _ _ _  C β α _ _  p ↔ @at_prop  _ _ _ C β α _ _ (Walk.copy p h₁ h₂)
:= by cases h₁ ; cases h₂ ; simp at *

lemma at_prop_cons_term_tail {V : Type} {G : SimpleGraph V} {n:ℕ} {C : EdgeColoring G (Fin n)} { α β : Fin n}
 {v₁ v₂ u: V} {h_adj : G.Adj v₂ v₁} {p : G.Walk v₁ u}
{h_at_prop: @at_prop _ _ _ C α β _ _ (Walk.cons h_adj (walk_terminal_tail p))}
: @at_prop _ _ _ C α β _ _ (walk_terminal_tail ( Walk.cons h_adj p )) := by
 induction p with
| nil =>
  simp [walk_terminal_tail] at *
  cases h_at_prop with
  |ab => simp at *
  |ba => rw [Walk.reverse_cons] ; simp ; exact at_prop.nil
| @cons v' u' w' h_adj₁ p₁ ih  =>
  simp_all [walk_terminal_tail]
  rw [ Walk.reverse_cons, append_tail_eq_tail_append]
  simp ; apply copy_at_prop.mp ; assumption ; apply reverse_not_nil ; apply Walk.not_nil_cons

lemma walk_terminal_tail_support {V : Type} {G : SimpleGraph V} {v u : V}
{p : G.Walk v u} : (walk_terminal_tail p).support ⊆ p.support := by
  cases p with
  |nil => simp [walk_terminal_tail]
  |cons =>
    rw [walk_terminal_tail]
    simp
    rw [ Walk.support_tail_of_not_nil ]
    · simp [List.tail_cons, Walk.support_append] ; apply List.subset_cons_of_subset ; apply List.dropLast_subset
    · apply reverse_not_nil ; apply Walk.not_nil_cons

lemma walk_terminal_tail_length {V : Type} {G : SimpleGraph V} {v u : V} {p : G.Walk v u}
{h_length : 0 < p.length } : (walk_terminal_tail p).length = p.length - 1 := by
  rw [walk_terminal_tail]
  simp
  apply Nat.succ_injective
  rw [ Nat.succ_eq_add_one, Walk.length_tail_add_one]
  · simp ; rw [ Nat.sub_add_cancel ] ; assumption
  · apply reverse_not_nil ; rw [  Walk.not_nil_iff_lt_length ] ; assumption

lemma terminal_tail_at_prop {V : Type} {G : SimpleGraph V} {n:ℕ} {C : EdgeColoring G (Fin n)}
{v u : V} {α β : Fin n} {p : G.Walk v u} (h_at_prop : @at_prop V G n C α β v u p)
: @at_prop V G n C β α v p.reverse.snd (@walk_terminal_tail V G v u p):= by
induction h_at_prop with
|nil => apply at_prop.nil
|ab p₁ h_prev h_adj h_color _ =>
apply at_prop_cons_term_tail
apply at_prop.ba
repeat assumption
apply Set.not_mem_subset walk_terminal_tail_support
repeat assumption
|ba p₁ h_prev h_adj h_color h_repeat₁ =>
cases p₁ with
|nil => apply at_prop.nil
|@cons _ p₂_initial _ h_adj₂ p₂  =>
have p_2_notnil : 0 < p₂.length  := by
  by_contra hp
  simp at hp
  have h_nil_2 : p₂.Nil := Walk.nil_iff_length_eq.mpr hp
  cases h_prev with
  |ab => contradiction
  |ba _ _ h_adj₃ h_color_2 h_repeat =>
    apply same_color_impossible h_adj h_adj₂.symm
    · simp at h_repeat₁
      have support_singleton : p₂.support = [p₂_initial] := by
        apply Walk.nil_iff_support_eq.mp
        assumption
      rw [support_singleton ] at h_repeat₁
      intro h_eq
      exact h_repeat₁.right (List.mem_singleton.mpr h_eq)
    · simp [Sym2.eq_swap] ; rw [h_color_2.symm] at h_color ; exact h_color
apply at_prop_cons_term_tail
apply at_prop.ab
· assumption
· apply Walk.not_nil_iff_lt_length.mpr ; rw [ walk_terminal_tail_length ] ; simp ; exact p_2_notnil ; simp
· assumption
· apply Set.not_mem_subset walk_terminal_tail_support ; assumption

lemma reverse_snd_concat {V : Type} {G : SimpleGraph V} {v u₁ u₂ : V} {p : G.Walk v u₁}
{h_adj : G.Adj u₁ u₂ } : (p.concat h_adj).reverse.snd = u₁ := by simp

lemma terminal_tail_concat_at_prop {V : Type} {G : SimpleGraph V} {v u₁ u₂ : V} {C : EdgeColoring G (Fin n)} { α β : Fin n}
{p : G.Walk v u₁} {h_adj : G.Adj u₁ u₂}
{h_at_prop: @at_prop _ _ _ C α β _ _ (Walk.copy (walk_terminal_tail (p.concat h_adj)) rfl reverse_snd_concat) }
: @at_prop _ _ _ C α β _ _  p := by
cases p with
| nil =>
exact at_prop.nil
| cons h_adj_1 p =>
have h_at_prop_noncopy
: @at_prop _ _ _ C α β _ _  (walk_terminal_tail ((Walk.cons h_adj_1 p).concat h_adj)) := copy_at_prop.mpr h_at_prop
rw [walk_terminal_tail, Walk.reverse_concat] at h_at_prop_noncopy
simp at *
exact copy_at_prop.mpr h_at_prop_noncopy

theorem concat_reverse {V : Type} {G : SimpleGraph V} {u v w : V} (p : G.Walk u v) (h : G.Adj u w) :
  p.reverse.concat h = (Walk.cons (G.symm h) p).reverse := by
  induction p with
  | nil => simp [ Walk.concat ]
  | cons h_edge p_ih => simp [ Walk.concat ]

lemma concat_copy {V : Type} {G : SimpleGraph V} {v₁ v₂ u v₁': V} {h_adj : G.Adj v₁ v₂}
  {h_adj' : G.Adj v₁' v₂} {p : G.Walk u v₁} { h₂ : v₁ = v₁' }
  : (p.copy rfl h₂).concat h_adj' = p.concat h_adj := by simp [Walk.copy] ; cases h₂ ; simp

lemma rev_adj_snd {V : Type} {G : SimpleGraph V} {v u : V} {p : G.Walk v u} (hp : ¬ p.Nil) :
    G.Adj u p.reverse.snd:= by
    apply @Walk.adj_snd V G u v p.reverse
    apply reverse_not_nil
    assumption

lemma reverse_elim {V : Type} {G : SimpleGraph V} {v u : V} {p₁ p₂ : G.Walk v u}
: p₁.reverse = p₂.reverse  ↔ p₁ = p₂  := by
constructor
· intro ; apply Walk.reverse_injective ; assumption
· intro h ; simp [h]

lemma tail_of_eq {V : Type} {G : SimpleGraph V} {v u: V} {p₁ p₂ : G.Walk v u}
 {h_snd: p₂.snd = p₁.snd} {_: p₁ = p₂}
: p₁.tail = p₂.tail.copy h_snd rfl := by
cases p₁ with
|nil => subst_vars ; simp
|cons h' p'  => subst_vars ; simp

-- lemma cons_term_tail {V : Type} {G : SimpleGraph V} {n:ℕ} {C : EdgeColoring G (Fin n)} { α β : Fin n}
--  {v₁ v₂ u: V} {h_adj : G.Adj v₂ v₁} {p : G.Walk v₁ u} {h_nil : ¬ p.Nil}
-- : (Walk.cons h_adj (walk_terminal_tail p)).copy rfl (cons_reverse_second h_nil) = walk_terminal_tail ( Walk.cons h_adj p ) := by
-- sorry


lemma concat_terminal_tail {V : Type} {G : SimpleGraph V} {v u z: V}
{p : G.Walk v z} {h_adj: G.Adj z u}
{h_eq : z =  ( p.concat h_adj ).reverse.snd}
: (walk_terminal_tail ( p.concat h_adj )) = p.copy rfl h_eq := by
simp [ walk_terminal_tail ]
have h₁ : p.copy rfl h_eq = (p.copy rfl h_eq).reverse.reverse := by simp
rw [h₁]
apply reverse_elim.mpr
have h_change : (p.concat h_adj).reverse.tail = (Walk.cons (G.symm h_adj) p.reverse).tail.copy (by simp) rfl := by
  apply tail_of_eq
  apply Walk.reverse_concat
rw [h_change ]
simp

lemma terminal_tail_concat {V : Type} {G : SimpleGraph V} {v u: V}
{p : G.Walk v u}  {h_nil : ¬ p.Nil}
: (walk_terminal_tail p).concat (rev_adj_snd h_nil).symm = p := by
induction p using @Walk.concatRec with
| Hnil => simp at h_nil
| Hconcat p' h'  a_ih =>
cases p' using @Walk.concatRec with
  | Hnil => simp [concat_terminal_tail]
  | Hconcat => rw [concat_terminal_tail, concat_copy] ; simp

lemma color_first_dart {V : Type} {G : SimpleGraph V} {n : ℕ} {C: EdgeColoring G (Fin n)}
{ α β : Fin n } {v u : V} {p: G.Walk v u} (h_nil : ¬ p.Nil) (h : @at_prop V G n C α β v u p )
: C ⟨s( u, p.reverse.snd), rev_adj_snd h_nil ⟩ = α := by
simp only [<-(h_second_penult h_nil) ]
induction h with
|nil=> simp at h_nil
|ab p _ h_adj _ _ a_ih =>
have h_pen : (Walk.cons h_adj p).penultimate = p.penultimate := by
  apply Walk.penultimate_cons_of_not_nil
  assumption
simp [h_pen]
apply a_ih
assumption
|ba p _ h_adj h_color _ a_ih =>
cases p with
|nil => simp [ Sym2.eq_swap ] ; exact h_color
|cons h₁ p₁ => simp [Walk.penultimate_cons_cons] ; apply a_ih ; simp

lemma alt_path_reverse_snd_unique {V : Type} {G : SimpleGraph V} {n : ℕ} {C: EdgeColoring G (Fin n)}
  { α β : Fin n} {v u : V} {w₁ w₂: G.Walk v u} {h_nil₁: ¬ w₁.Nil} {h_nil₂: ¬ w₂.Nil}
  {h₁ : @at_prop _ _ _ C α β v u w₁} {h₂ : @at_prop _ _ _ C α β v u w₂}
  : w₁.reverse.snd = w₂.reverse.snd := by
have h_u1 : G.Adj w₁.reverse.snd u:= by symm; exact rev_adj_snd h_nil₁
have h_u2 : G.Adj w₂.reverse.snd u:= by symm; exact rev_adj_snd h_nil₂
have h_color₁ :  C ⟨s( w₁.reverse.snd, u), h_u1 ⟩ = α := by simp [Sym2.eq_swap] ; exact color_first_dart h_nil₁ h₁
have h_color₂ :  C ⟨s( w₂.reverse.snd, u), h_u2 ⟩ = α := by simp [Sym2.eq_swap] ; exact color_first_dart h_nil₂ h₂
by_contra h_neq
apply same_color_impossible h_u1 h_u2
exact h_neq
rw [ <- h_color₂] at h_color₁
exact h_color₁

lemma at_prop_subsingleton {V : Type} {G : SimpleGraph V} {n : ℕ} {C: EdgeColoring G (Fin n)}
   { α β : Fin n} {v u : V} : Subsingleton {w : G.Walk v u //  @at_prop V G n C α β v u w } := by
constructor
intro ⟨w₁, h₁⟩ ⟨w₂, h₂⟩
apply Subtype.ext
simp
let motive : ∀ (v u : V), G.Walk v u → Prop :=
  λ v u p => ∀ α β, (@at_prop V G n C α β v u p → ∀ w₂ : G.Walk v u, @at_prop V G n C α β v u w₂ → p = w₂)
apply @Walk.concatRec V G motive
· intros
  simp [motive]
  intros
  apply Eq.symm
  rw [ <-Walk.isPath_iff_eq_nil]
  apply at_prop_path
  assumption
· intro v' z u' w₁' h_adj a_ih α β h₁ w₂' h₂
  cases w₂' with
  |nil =>
  rw [ <-Walk.isPath_iff_eq_nil]
  apply at_prop_path
  assumption
  |cons a p =>
  simp [motive] at a_ih
  let tail₁ := walk_terminal_tail (w₁'.concat h_adj)
  let tail₂ := walk_terminal_tail (Walk.cons a p)
  have h₁_tail := terminal_tail_at_prop h₁
  have h₂_tail := terminal_tail_at_prop h₂
  change at_prop tail₁ at h₁_tail
  change at_prop tail₂ at h₂_tail
  have h_rev_snd : (w₁'.concat h_adj).reverse.snd = z  := by simp
  have h_rev_snd_2 : (Walk.cons a p).reverse.snd = z  := by
    rw [<-h_rev_snd]
    apply alt_path_reverse_snd_unique
    repeat simp [Walk.concat, Walk.not_nil_iff_lt_length]
    repeat assumption
  have h₁_tail_copy : @at_prop _ _ _ C β α _ _ (Walk.copy tail₁ rfl h_rev_snd) := by apply copy_at_prop.mp; apply h₁_tail
  have h₂_tail_copy : @at_prop _ _ _ C β α _ _ (Walk.copy tail₂ rfl h_rev_snd_2) := by apply copy_at_prop.mp; apply h₂_tail
  have h_p1 : @at_prop _ _ _ C β α _ _ w₁' := @terminal_tail_concat_at_prop _ _ _ _ _ _ _ _ _ _ _ h₁_tail_copy
  specialize a_ih β α h_p1 (Walk.copy tail₂ rfl h_rev_snd_2) h₂_tail_copy
  simp [a_ih, tail₂, Walk.copy]
  cases h_rev_snd_2
  simp
  apply terminal_tail_concat
  simp
repeat assumption

def R_reach {V : Type} {G : SimpleGraph V} {n: ℕ}
 {C: EdgeColoring G (Fin n)} {α β : Fin n} {v: V}
: V → Prop := fun z => ∃ p : G.Walk z v, @at_prop V G n C α β z v p

lemma extend_at_prop {V : Type} {G : SimpleGraph V} {n : ℕ} {C : EdgeColoring G (Fin n)}
{α β : Fin n} {v u z : V} (p : G.Walk v u) (h_at : @at_prop V G n C β α v u p)
(h_adj : G.Adj u z) (h_sup : z ∉ p.support) {h_c : C ⟨ s(u,z), G.mem_edgeSet.mp h_adj ⟩  = α }
: @at_prop V G n C α β v z (p.concat h_adj) := by
induction p with
| nil =>
apply at_prop.ba ; apply at_prop.nil
assumption
simp
exact  G.ne_of_adj h_adj
| cons h' p' a_ih =>
change at_prop (Walk.cons h' (p'.concat h_adj))
cases h_at with
| ab _ _ _ h_col_prev h_rep =>
simp at h_sup
push_neg at h_sup
apply at_prop.ba
apply a_ih
assumption
exact h_sup.2
repeat assumption
simp
exact ⟨ h_rep , h_sup.1.symm ⟩
| ba _ _ _ h_col_prev h_rep =>
simp at h_sup
push_neg at h_sup
apply at_prop.ab
apply a_ih
assumption
exact h_sup.2
repeat assumption
exact concat_not_nil
assumption
simp
exact ⟨ h_rep , h_sup.1.symm ⟩

lemma extend_alternating_path {V : Type} {G : SimpleGraph V} {n : ℕ} {C : EdgeColoring G (Fin n)}
  {α β : Fin n} {ℓ₂ ℓ₁ u v : V} {f: edgeSet G}
  (p : G.Walk ℓ₁ u) (h_used : @edge_used V G n C β α u ℓ₁ ℓ₂ p f)
  (h_adj : G.Adj u v) (h_sup : v ∉ insert ℓ₂ p.support) {h_c : C ⟨ s(u,v), G.mem_edgeSet.mp h_adj ⟩  = α }
  : @R_ed_y V G v n C α β f := by
  obtain ⟨ h_ed, h_at ⟩ := h_used
  cases p using @Walk.concatRec with
  | Hnil =>
    use ℓ₁, ℓ₂, Walk.cons h_adj Walk.nil
    refine { h_ed := ?_, alt_prop := ?_ }
    · assumption
    · apply at_prop.ab ; apply at_prop.ba ; apply at_prop.nil
      assumption ; simp ; exact G.ne_of_adj h_adj ; simp
      have h_c' : C ⟨s(ℓ₂, _), adj_of_edge h_ed ⟩ = β := by
        cases h_at with
        | ab => simp at *
        | ba => assumption
      repeat exact h_c'
      simp at *
      constructor
      · exact G.ne_of_adj (adj_of_edge h_ed)
      · intro h ; simp [h, insert] at h_sup
  | Hconcat p' h' =>
  let tail := walk_terminal_tail (p'.concat h')
  use ℓ₁, ℓ₂, (p'.concat h').concat h_adj
  refine { h_ed := ?_, alt_prop := ?_ }
  · assumption
  · simp [<- Walk.concat_cons]
    apply extend_at_prop
    · exact h_at
    · simp [insert] at * ; assumption
    · assumption

lemma list_droplast {l: List T} {h_nil: l ≠ []}: l.dropLast ⊆ l := by
induction l with
|nil => simp
|cons _ l' a_ih  =>
  cases l' with
  | nil => simp
  |cons =>
  simp [List.dropLast_cons_of_ne_nil]
  intro x hx
  specialize a_ih hx
  repeat simp at *
  exact Or.inr a_ih

lemma reverse_tail_support {V : Type} {G : SimpleGraph V} {v u :V} {p : G.Walk v u} {h_nil: ¬ p.Nil} :
    p.reverse.tail.support ⊆  p.support := by
    rw [Walk.support_tail_of_not_nil]
    simp
    apply @list_droplast V p.support
    simp
    exact reverse_not_nil h_nil

lemma term_tail_support {V : Type} {G : SimpleGraph V} {v u :V} {p : G.Walk v u}
{h_nil: ¬ p.Nil} {h_path : p.IsPath}
: u ∉ p.reverse.tail.support := by
induction p with
|nil => simp at h_nil
|@cons a b d h' p' a_ih =>

  rw [ Walk.reverse_cons ]
  cases p' with
  |nil => simp ; exact G.ne_of_adj h'.symm
  | @cons a' c c' h'' p'' =>
    rw [append_tail_eq_tail_append]
    simp at *
    constructor
    · exact a_ih h_path.1.1 h_path.1.2
    · exact ⟨ by intro h₁ ; simp [<-h₁] at h_path, by intro h₂ ; simp [<-h₂] at h_path ⟩
    · simp ; apply append_not_nil ; simp

lemma extend_reachable (f₁ f₂ : ( edgeSet G )) (h_adj : (lineGraph G).Adj f₁ f₂)
(f₁_reachable: @R_ed_y V G v n C α β f₁) (γ δ : (Fin n)) {h_δv: β ∉ C '' (edgeSpan G v)}
( h_color₁ : C f₁ = γ ) (h_color₂ : C f₂ = δ ) (h_γαβ : γ = α ∨ γ = β ) (h_δαβ : δ = α ∨ δ = β) (h_γδ : γ ≠ δ )
: @R_ed_y V G v n C α β f₂ := by
obtain ⟨ℓ₁, ℓ₂, p,  hp ⟩ := f₁_reachable
have h_ed : s(ℓ₂, ℓ₁) = f₁ := hp.h_ed
have h_at_p := hp.alt_prop
cases h_γαβ with
|inl h_γα =>
  rw [h_γα] at h_γδ
  have h_δβ : δ = β := Or.resolve_left h_δαβ h_γδ.symm
  rw [h_δβ] at h_γδ
  rw [h_γα] at h_color₁
  rw [h_δβ] at h_color₂
  have hv : v ∉ ( f₂ : Sym2 V) := by
    intro hv₁
    have h_β : β ∈ ⇑C '' edgeSpan G v := by
      use f₂
      exact ⟨ hv₁, h_color₂ ⟩
    contradiction
  obtain ⟨ ℓ₂', ℓ₁', p', hp' ⟩ := extend_reachable_αβ α β f₁ f₂ h_adj hv hp h_color₁ h_color₂ h_γδ
  use ℓ₂', ℓ₁', p'
  exact hp'.1
|inr h_γα =>
rw [h_γα] at h_γδ
have h_δα : δ = α := Or.resolve_right h_δαβ h_γδ.symm
rw [h_δα] at h_γδ
rw [h_γα] at h_color₁
rw [h_δα] at h_color₂
cases h_at_p with
| @ab _ _ _ _ h_prev _ h_nil _ h_rep =>
  let tail := walk_terminal_tail p
  have h_tail := terminal_tail_at_prop h_prev
  have h_used_tail : @edge_used V G n C β α p.reverse.snd ℓ₁ ℓ₂ tail f₁  := by
    refine { h_ed := ?_, alt_prop := ?_ }
    · assumption
    · apply at_prop.ba
      exact h_tail
      assumption
      simp [tail, walk_terminal_tail]
      intro h
      exact h_rep ((@reverse_tail_support _ _ _ _ p h_nil) h)

  have h_fd : C ⟨s( v, p.reverse.snd), rev_adj_snd h_nil ⟩ = α := color_first_dart h_nil h_prev
  by_cases hv: v ∈ (f₂ : Sym2 V)
  · let os := Sym2.Mem.other hv
    use v, os, Walk.nil' v
    have adj_rev : G.Adj os v := by symm ; apply adj_of_edge (Sym2.other_spec hv)
    have h_neq : os ≠ v := G.ne_of_adj adj_rev
    have h_other_spec : s(v,os) = f₂ := Sym2.other_spec hv
    refine { h_ed := ?_, alt_prop := ?_ }
    · simp [Sym2.eq_swap] ; assumption
    · apply at_prop.ba ; apply at_prop.nil ; simp [Sym2.eq_swap, h_other_spec] ; exact h_color₂ ;
      simp ; push_neg ; assumption
  ·
    have h_snd : p.reverse.snd ∉ (f₂ : Sym2 V):= by
      intro h
      rw [<-h_color₂] at h_fd
      apply same_color_helper f₂ h_fd
      repeat assumption
    obtain ⟨ ℓ₁', ℓ₂', p', hp' ⟩ := extend_reachable_αβ β α f₁ f₂ h_adj h_snd h_used_tail h_color₁ h_color₂ h_γδ
    apply extend_alternating_path
    · exact hp'.1
    · simp [insert]
      constructor
      · intro h₁ ; obtain ⟨ h₂, _ ⟩ := hp'.1 ; rw [<-h₂, h₁] at hv ; simp at hv
      · have h_vℓ₂ : v ≠ ℓ₂ := by
          intro h₁
          have h_neq : ℓ₂ ≠ ℓ₁ := G.ne_of_adj (adj_of_edge h_ed)
          have h_β : β ∈ ⇑C '' edgeSpan G v := by
            rw [h₁] ; use f₁
            exact ⟨ ((Sym2.mem_and_mem_iff h_neq).mpr h_ed.symm).1, h_color₁ ⟩
          contradiction
        intro h₁
        rcases hp' with ⟨ h₂, h₃ ⟩
        specialize h₃ h₁
        simp [insert, h_vℓ₂, tail, walk_terminal_tail] at h₃
        have h_contra : v ∉ p.reverse.tail.support := by
          apply term_tail_support
          assumption
          apply at_prop_path
          assumption
        contradiction
    · simp [Sym2.eq_swap] ; assumption
    · exact (rev_adj_snd h_nil).symm
| ba _ _ _  h_col =>
  have h₄ : C ⟨f₁, f₁.property ⟩ = α := by simp [<-h_ed ] ; assumption
  rw [h₄ ] at h_color₁
  symm at h_γδ
  contradiction

variable [F : Fintype (neighborSet G v)]

noncomputable instance : Fintype (edgeSpan G v) := by
  exact Fintype.ofEquiv (neighborSet G v) (neighborSetedgeSpanEquiv G v)

theorem edgeSpan_card_eq_degree : (edgeSpan G v).toFinset.card = G.degree v := by
  have h_card : Fintype.card (neighborSet G v) = Fintype.card (edgeSpan G v) := by
    rw [<- Fintype.card_congr  (neighborSetedgeSpanEquiv G v) ]
  have h_degree : G.degree v = Fintype.card (neighborSet G v) := by simp
  rw [ h_degree, h_card ]
  exact Set.toFinset_card (edgeSpan G v)

-- Note: this should exist
-- instance [Fintype V] : Fintype (Sym2 V) := sorry

def insertEdges (t : Set (Sym2 V)) (G : SimpleGraph V) : SimpleGraph V :=
  fromEdgeSet (t ∪ edgeSet G)

instance : Insert (Sym2 V) (SimpleGraph V) where
  insert := fun e G => fromEdgeSet (insert e <| edgeSet G)

-- instance equivSimpleGraphNonDiagSym2 : Equiv (SimpleGraph V) { s : Set <| Sym2 V // s ∩ Sym2.IsDiag = ∅ } where
--   toFun := fun G => by
--     refine sorry
--   invFun := sorry
--   left_inv := sorry
--   right_inv := sorry

lemma isEmpty_iff_alt [h:  IsEmpty (Sym2 (∅ : Set V ))] : ((Sym2 (∅ : Set V )) → False) := by
exact fun a => IsEmpty.false a

lemma lineGraph_bot_is_bot :  lineGraph ( ⊥ : ( SimpleGraph V) ) = ⊥  := by
refine edgeSet_eq_empty.mp ?_
by_contra h
push_neg at h
obtain ⟨ e ⟩ := h
simp at e
exact isEmpty_iff_alt e

lemma line_graph_empty : lineGraph (fromEdgeSet ( ∅ : Set (Sym2 V))) = ⊥ := by
rw [fromEdgeSet_empty]
rw [lineGraph_bot_is_bot]

instance : IsEmpty (edgeSet (fromEdgeSet ( ∅ : Set (Sym2 V)))) := by rw [fromEdgeSet_empty] ; simp

lemma insert_edgeset_diag {V : Type} [ Fintype V] [DecidableEq V]
(e : (Sym2 V)) (h: e.IsDiag) (S : Set (Sym2 V)) :  fromEdgeSet (insert e S)  = fromEdgeSet S:= by
simp only [fromEdgeSet]
ext u v
constructor
· intro h_uv
  simp at *
  rcases h_uv with ⟨ h₁, h₂ ⟩
  cases h₁ with
  | inl h_e =>
    have h_diag : Sym2.IsDiag (s(u, v)) := by rw [h_e]; exact h
    contradiction
  | inr h_mem => exact ⟨h_mem, h₂⟩
· intro inv_uv
  simp at *
  rw [and_comm]
  constructor
  · exact inv_uv.right
  · apply Or.inr
    exact inv_uv.left

lemma insert_edgeset_incidenceSet { V : Type } {v:V} [ Fintype V ] [ DecidableEq V] (e : (Sym2 V))
{S : Finset (Sym2 V)} :
(fromEdgeSet (insert e S)).incidenceSet v ⊆ insert e ((fromEdgeSet S).incidenceSet v)
:= by
intro f hf
simp [incidenceSet, mem_filter, Sym2.mem_iff] at *
rcases hf with ⟨hf_mem, hv_in_f⟩
rcases hf_mem with ⟨h_mem, h_not_diag⟩
cases h_mem with
| inl heq => left ; exact heq
| inr h_in_S => right ; exact ⟨⟨h_in_S, h_not_diag⟩, hv_in_f⟩

lemma insert_edgeset {V : Type} [ Fintype V] [ DecidableEq V] {e : (Sym2 V)} {S : Finset (Sym2 V)} (h_eS : e ∉ S) :
 (edgeSet (fromEdgeSet S.toSet)) = edgeSet (fromEdgeSet ((insert e S).toSet)) \ ( {e} : Set (Sym2 V) ):= by
simp
ext f
constructor
· simp
  intro hS hf
  have hfe : e ≠ f := by
    intro heq
    rw [ heq ] at h_eS
    contradiction
  exact ⟨⟨Or.inr hS, hf⟩, Ne.symm hfe⟩
· simp
  intro hfeS hf hfe
  exact ⟨hfeS.resolve_left hfe, hf⟩

lemma max_degree_mono  {V : Type} [ Fintype V] [ DecidableEq V]  {G H : SimpleGraph V} {h_mono : G ≤ H} :
maxDegree ( G ) ≤ maxDegree ( H ) := by
apply maxDegree_le_of_forall_degree_le
intro v
have h_GH_v : (G.degree v) ≤ (H.degree v) := by
  simp [ <- card_neighborFinset_eq_degree ]
  apply card_le_card
  intro w hw
  simp at *
  exact h_mono hw
have h_2 : (H.degree v) ≤ maxDegree ( H ) := by apply degree_le_maxDegree
exact le_trans h_GH_v h_2

lemma insert_back_degrees {V : Type} [ Fintype V] [ DecidableEq V ]  {e : (Sym2 V)} {S : Finset (Sym2 V)} :
maxDegree ( (fromEdgeSet S.toSet)) ≤ maxDegree ( fromEdgeSet ((insert e S).toSet) )
∧ maxDegree ( fromEdgeSet ((insert e S).toSet) ) ≤ maxDegree ( (fromEdgeSet S.toSet)) + 1 := by
constructor
· apply max_degree_mono
  apply fromEdgeSet_mono
  simp
· simp
  apply maxDegree_le_of_forall_degree_le
  intro v
  trans (fromEdgeSet S).degree v + 1
  · simp [ <- card_incidenceSet_eq_degree ]
    simp_rw [←Set.toFinset_card]
    trans  #(insert e ((fromEdgeSet S).incidenceSet v).toFinset)
    · apply card_le_card ; simp ; apply insert_edgeset_incidenceSet ;
    · apply card_insert_le
  · simp ; apply degree_le_maxDegree

lemma degree_eq_card_edgeSpan : Finset.card (Set.toFinset (edgeSpan G v))  = G.degree v:= by
rw [<-card_neighborSet_eq_degree]
apply Eq.symm
rw [Set.toFinset_card]
apply Fintype.card_congr (neighborSetedgeSpanEquiv G v)

theorem edgeSpan_card_le_edgeChromaticNumber  :
 (edgeSpan G v).toFinset.card ≤ edgeChromaticNumber G := by
  have h_same : edgeSpan G v = (edgeSpan G v).toFinset := by
    exact Eq.symm (Set.coe_toFinset (edgeSpan G v))
  have h_s : (lineGraph G).IsClique (edgeSpan G v).toFinset := by
    rw [<-h_same]
    exact edgeSpan_isClique G v
  exact IsClique.card_le_chromaticNumber h_s

theorem degree_le_edgeChromaticNumber : G.degree v ≤  edgeChromaticNumber G := by
  rw [<- edgeSpan_card_eq_degree]
  exact edgeSpan_card_le_edgeChromaticNumber G v

variable [ Fintype V ]

lemma empty_zero_max_degree : maxDegree (⊥ : SimpleGraph V) = 0 := by
apply Nat.le_antisymm
· apply maxDegree_le_of_forall_degree_le
  intro v
  have h: degree ⊥ v = 0 := bot_degree v
  exact Nat.le_zero.mpr h
· exact Nat.zero_le (maxDegree ⊥)

lemma subset_card_ne_implies_nonempty_diff [DecidableEq T] {s t : Set T} [Fintype s] [Fintype t]
  (hst : s.toFinset ⊆ t.toFinset) (hcard : 0 < (t.toFinset).card - (s.toFinset).card) : Nonempty ( Set.diff t s ) := by
have hdiff : 0 < card ((t.toFinset) \ (s.toFinset)) := by
  rw [Finset.card_sdiff hst]
  exact hcard
rw [Finset.card_pos] at hdiff
simp
obtain ⟨ w , hw ⟩ := hdiff
use w
simp only [Set.mem_toFinset, Finset.mem_sdiff] at hw
exact hw

-- lemma incidence_edgespan : (edgeSpan G v) = ( incidenceSet G v ) := sorry

--Given a graph G, a vertex u ∈ V(G), and a function C: E(G) → (Δ+1),
--then we obtain a proof that there is at least one color missing in the neighbourhood of u
def missing_color (G : SimpleGraph V) [DecidableRel G.Adj] (C : (edgeSet G) → (Fin ( G.maxDegree + 1))) (u : V)
: ∃β : (Fin ( G.maxDegree + 1)), β ∉ (C '' (edgeSpan G u)) := by
have h_sub : ( (C '' (edgeSpan G u)).toFinset) ⊆ ((@Set.univ (Fin ( G.maxDegree + 1))).toFinset):= by simp
have hcard : 0 < ((@Set.univ (Fin ( G.maxDegree  + 1))).toFinset).card - ((C '' (edgeSpan G u)).toFinset).card := by
  simp
  rw [Nat.lt_succ_iff]
  trans Finset.card (Set.toFinset (edgeSpan G u))
  · exact card_image_le
  · rw [degree_eq_card_edgeSpan]
    exact degree_le_maxDegree G u
obtain ⟨ β, hβ ⟩ := subset_card_ne_implies_nonempty_diff h_sub hcard
use β
dsimp [Set.diff] at *
exact hβ.2

abbrev eg ( S: Finset (Sym2 V) ) : SimpleGraph V := (fromEdgeSet (toSet S)) --edge-induced-graph

def prop_to_use : Finset (Sym2 V) → Prop :=
fun S => Colorable (lineGraph (fromEdgeSet (toSet S))) (maxDegree (fromEdgeSet (toSet S)) + 1)

lemma empty_graph_easy : (prop_to_use (∅ : Finset (Sym2 V)) ) := by
rw [prop_to_use]
rw [coe_empty]
simp
rw [line_graph_empty]
rw [ empty_zero_max_degree ]
simp
have h₂ : 0 ≤ 1 := by exact Nat.zero_le 1
apply Colorable.mono h₂
apply @colorable_of_isEmpty

noncomputable instance induced_decidable {V : Type} [ Fintype V ] [ DecidableEq V ] {S : Finset (Sym2 V)}
: DecidableRel ( (fromEdgeSet (toSet S)).Adj ) := by exact Classical.decRel ((fromEdgeSet (toSet S)).Adj)

lemma path_concat {V : Type} {G : SimpleGraph V} {v u₁ u₂: V}
{p: G.Walk v u₁} {h_adj: G.Adj u₁ u₂} (h_path : (p.concat h_adj).IsPath) : p.IsPath := by
simp [Walk.concat] at h_path
exact Walk.IsPath.of_append_left h_path

lemma extending_missing_same {V : Type} [ Fintype V ] [ DecidableEq V ]
{S : Finset (Sym2 V)} {e: Sym2 V} (h_eS: e ∉ S) {n: ℕ} (α: (Fin n))
{C: EdgeColoring (eg S) (Fin n)} {x y :V} (h_exy : e = s(x,y))
(h_xα: α ∉ (C '' (edgeSpan (eg S) x))) (h_yβ: α ∉ (C '' (edgeSpan (eg S) y)))
: Colorable (lineGraph (eg (insert e S))) n := by
let G_S := eg S
let G_host := (eg (insert e S))
change Colorable (lineGraph G_host ) n
have hC : ∀ {a b : ↑(edgeSet G_S)}, Adj (lineGraph G_S) a b → Adj ⊤ (C a) (C b) := by
  intro f₁ f₂ h₁₇
  change Ne (C f₁) (C f₂)
  exact Coloring.valid C h₁₇

have h_set_diff : (edgeSet G_S )  = edgeSet G_host \ ( {e} : Set (Sym2 V) ) := by
    dsimp
    exact insert_edgeset h_eS

let C_extension_alt : edgeSet G_host → (Fin n) := fun f =>
if h_ef: f = e then α else
have h_f : f.val ∈ (edgeSet G_S) := by
  rw [ h_set_diff ]
  exact ⟨f.2, h_ef⟩
(C ⟨ f, h_f ⟩)
use C_extension_alt
intro f₁ f₂ h_adj
change Ne (C_extension_alt f₁) (C_extension_alt f₂)
intro h_same_color
have h_diff : f₁ ≠ f₂ := by exact Adj.ne h_adj
have h_diff_sym2 : (f₁ :Sym2 V) ≠ (f₂ :Sym2 V) := @lift_edge_type V G_host f₁ f₂ h_diff

have symmetric_argument_f12 (f₁ f₂ : edgeSet G_host ) (h_1e : (f₁ : Sym2 V) = e)
  (h_diff_sym2 : (f₁ : Sym2 V) ≠ (f₂ : Sym2 V) ) (h_same_color : C_extension_alt f₁ = C_extension_alt f₂)
  (h_adj : Adj (lineGraph G_host) f₁ f₂) : False := by
  have h_1eval : C_extension_alt f₁ = α  := by dsimp [C_extension_alt] ; simp [h_1e]
  have h_2e : (f₂ :Sym2 V) ≠ e := by rw [h_1e] at h_diff_sym2 ; exact Ne.symm h_diff_sym2
  have h_2G_S : (f₂ :Sym2 V) ∈ (edgeSet G_S) := by rw [ h_set_diff ] ; exact ⟨ f₂.property, h_2e⟩
  have h_2eval : C_extension_alt f₂ = C ⟨f₂, h_2G_S ⟩  := by dsimp [C_extension_alt] ; simp [h_2e]
  rw [ h_1eval, h_2eval  ] at h_same_color
  rw [Adj, lineGraph ] at h_adj
  simp only at h_adj
  unfold Adjacent at h_adj
  obtain ⟨ z, hz ⟩ := h_adj.left
  rw [ AdjacentAt, h_1e  ] at hz
  rcases hz with ⟨hz_e, hz_f₂⟩
  have h_zxy : z = x ∨ z = y := by rw [h_exy] at hz_e ; exact Sym2.mem_iff.mp hz_e
  cases h_zxy with
  | inl h_zx  =>
  rw [<-h_zx ] at h_xα
  have h_contra: α ∈ C '' edgeSpan (eg S) z := by
    use ⟨ f₂ , h_2G_S ⟩
    exact ⟨ hz_f₂ , h_same_color.symm ⟩
  contradiction
  | inr h_zy =>
  rw [<-h_zy ] at h_yβ
  have h_contra: α ∈ C '' edgeSpan (eg S) z := by
    use ⟨ f₂ , h_2G_S ⟩
    exact ⟨ hz_f₂ , h_same_color.symm ⟩
  contradiction

by_cases h_1e : (f₁ :Sym2 V) = e
· exact symmetric_argument_f12 f₁ f₂ h_1e h_diff_sym2 h_same_color h_adj
· by_cases h_2e : (f₂ :Sym2 V) = e
  · exact symmetric_argument_f12 f₂ f₁ h_2e h_diff_sym2.symm h_same_color.symm h_adj.symm
  · have h_1G_S : (f₁ :Sym2 V) ∈ (edgeSet G_S) := by rw [ h_set_diff ] ; exact ⟨ f₁.2, h_1e⟩
    have h_2G_S : (f₂ :Sym2 V) ∈ (edgeSet G_S) := by rw [ h_set_diff ] ; exact ⟨ f₂.2, h_2e⟩
    have h_12eval : C ⟨f₁, h_1G_S ⟩ = C ⟨f₂, h_2G_S ⟩  := by dsimp [C_extension_alt] at h_same_color ; simp [h_1e, h_2e] at h_same_color ; exact h_same_color
    have adjacent_line_G_S : Adj (lineGraph G_S) ⟨f₁, h_1G_S ⟩ ⟨f₂, h_2G_S ⟩ := by
      rw [Adj , lineGraph]
      constructor
      · rw [Adj, lineGraph] at h_adj
        exact h_adj.left
      · intro hf12
        rw [Subtype.mk.injEq] at hf12
        exact h_diff_sym2 hf12

    have h_adj_top : Adj ⊤ (C ⟨f₁, h_1G_S ⟩) (C ⟨f₂, h_2G_S ⟩) := hC adjacent_line_G_S
    rw [ h_12eval ] at h_adj_top
    simp at h_adj_top

lemma extending_edge_coloring_helper {V : Type} [ Fintype V ] [ DecidableEq V ]
{S : Finset (Sym2 V)} {e: Sym2 V} {h_eS: e ∉ S } {n: ℕ} {α β : (Fin n)}
{C: EdgeColoring (eg S) (Fin n)} {x y :V} {h_exy : e = s(x,y) }
{h_xα: α ∉ (C '' (edgeSpan (eg S) x)) } {{h_yβ: β ∉ (C '' (edgeSpan (eg S) y)) }}
{hp : ¬ @R_reach V (eg S) n C α β y x }
: Colorable (lineGraph (eg (insert e S))) n := by
let G_S := eg S
let G_host := (eg (insert e S))
change Colorable (lineGraph G_host ) n
have hC : ∀ {a b : ↑(edgeSet G_S)}, Adj (lineGraph G_S) a b → Adj ⊤ (C a) (C b) := by
  intro f₁ f₂ h₁₇
  change Ne (C f₁) (C f₂)
  exact Coloring.valid C h₁₇

have h_set_diff : (edgeSet G_S )  = edgeSet G_host \ ( {e} : Set (Sym2 V) ) := by
    dsimp
    exact insert_edgeset h_eS

by_cases h_ab : α = β
· -- Assume α = β is missing in both x and y, then color e by α
  rw [<-h_ab] at h_yβ
  exact extending_missing_same h_eS α h_exy h_xα h_yβ

· -- Assume α ≠ β, interchange α and β
  let R_y : V → Prop := fun z => @R_reach V G_S n C α β y z
  let E_y : edgeSet G_S → Prop := fun f =>
    ∃ (ℓ₁ ℓ₂ : V), ∃ (p: G_S.Walk ℓ₁ y), @edge_used V G_S n C α β y ℓ₁ ℓ₂ p f

  let C_alt : (edgeSet G_S → (Fin n)) := fun f =>
    if E_y f then
      if C f = α then β
      else if C f = β then α
      else C f
    else C f

  let C_extension_alt : edgeSet G_host → (Fin n) := fun f =>
  if h_ef: f = e then α
  else
  have h_f : f.val ∈ (edgeSet G_S) := by
    rw [ h_set_diff ]
    exact ⟨f.2, h_ef⟩
  C_alt ⟨ f, h_f ⟩

  use C_extension_alt

  have h_e_f (f₁ f₂ : (edgeSet G_host )) (h_1e : (f₁:Sym2 V) = e)
  (h_adj : (lineGraph G_host).Adj f₁ f₂)
  : (C_extension_alt f₁ ≠ C_extension_alt f₂) := by
    have h_1eval : C_extension_alt f₁ = α  := by dsimp [C_extension_alt] ; simp [h_1e]
    by_contra h_same_color
    have h_diff : f₁ ≠ f₂ := by exact Adj.ne h_adj
    have h_diff_sym2 : (f₁ :Sym2 V) ≠ (f₂ :Sym2 V) := by intro h' ; exact h_diff (Subtype.coe_inj.mp h' )
    have h_2e : (f₂ :Sym2 V) ≠ e := by rw [h_1e] at h_diff_sym2 ; exact Ne.symm h_diff_sym2
    have h_2G_S : (f₂ :Sym2 V) ∈ (edgeSet G_S) := by rw [ h_set_diff ] ; exact ⟨ f₂.property, h_2e⟩
    have h_2eval : C_extension_alt f₂ = C_alt ⟨f₂, h_2G_S ⟩  := by dsimp [C_extension_alt] ; simp [h_2e]
    rw [ h_2eval, h_1eval ] at h_same_color
    dsimp [C_alt ] at h_same_color

    have touching_e_impossible_β ( hz_f₂ : Sym2.Mem y f₂ )
    (change_β_2_α : C ⟨ f₂, h_2G_S ⟩  = β  )
    : False := by
      have h_f2_span_y :  ⟨ f₂, h_2G_S ⟩ ∈ (edgeSpan G_S y) := by exact hz_f₂
      have h_β_in_image : β ∈ C '' edgeSpan G_S y := by use ⟨ f₂, h_2G_S ⟩
      contradiction

    have touching_e_impossible_α ( hz_f₂ : Sym2.Mem x f₂ )
    (colored_α : α = C { val := ↑f₂, property := h_2G_S } )
    : False := by
      have h_f2_span_x :  ⟨ f₂, h_2G_S ⟩ ∈ (edgeSpan G_S x) := by exact hz_f₂
      have h_α_in_image : α ∈ C '' edgeSpan G_S x := by use ⟨ f₂, h_2G_S ⟩ ; exact ⟨ h_f2_span_x , colored_α.symm ⟩
      contradiction

    simp [Adj, lineGraph] at h_adj
    unfold Adjacent at h_adj
    obtain ⟨ z, hz ⟩ := h_adj.left
    rw [ AdjacentAt, h_1e  ] at hz
    rcases hz with ⟨hz_e, hz_f₂⟩
    have h_zxy : z = x ∨ z = y := by rw [h_exy] at hz_e ; exact Sym2.mem_iff.mp hz_e
    split_ifs at h_same_color with exists_trail change_α_2_β change_β_2_α
    · --DONE exists_trail, change_α_2_β
      exact h_ab h_same_color
    · --DONE exists_trail, change_β_2_α
      cases h_zxy with
      | inl  h_zx =>
        rcases exists_trail with ⟨ℓ₁, ℓ₂, p, h_ed, alt_prop⟩
        have h_x_mem : x = ℓ₁ ∨ x = ℓ₂ := by rw [ h_zx, <- h_ed, Sym2.mem_iff'] at hz_f₂ ; exact hz_f₂.symm
        have yx_trail: (R_y x) := by
          dsimp [R_y, R_reach ]
          cases h_x_mem with
          | inl h_x_v₁ => rw [h_x_v₁] ; use p ; cases alt_prop ; repeat assumption
          | inr h_x_v₂ => rw [h_x_v₂] ; use (Walk.cons (adj_of_edge h_ed) p)
        exact hp yx_trail
      | inr  h_zy =>
        rw [ h_zy ] at hz_f₂
        exact touching_e_impossible_β hz_f₂ change_β_2_α
    · -- DONE exists_trail, neither α nor β, no change
      exact change_α_2_β h_same_color.symm
    · -- DONE exists NO trail, no change
      cases h_zxy with
      | inl  h_zx =>
        rw [ h_zx ] at hz_f₂
        exact touching_e_impossible_α hz_f₂ h_same_color
      | inr  h_zy =>
        rw [ h_zy ] at hz_f₂
        let other := Sym2.Mem.other hz_f₂
        have h_f₂_eq : s(other, y) = ↑f₂  := by rw [Sym2.eq_swap] ; exact Sym2.other_spec hz_f₂
        have h_adj_trail : G_S.Adj other y := by apply @adj_of_edge V G_S y other ⟨ f₂, h_2G_S⟩ h_f₂_eq

        have h_used : E_y ⟨ f₂, h_2G_S⟩  := by
          simp [E_y]
          use y, other, Walk.nil' y
          refine { h_ed := ?_, alt_prop := ?_ }
          · exact h_f₂_eq
          · apply at_prop.ba ; exact at_prop.nil ; symm ;
            simp [<- h_f₂_eq] at h_same_color ; exact h_same_color ; simp ; exact (Adj.ne h_adj_trail )
        exact exists_trail h_used

  intro f₁ f₂ h_adj
  change (C_extension_alt f₁) ≠ (C_extension_alt f₂)
  have h_diff : f₁ ≠ f₂ := by exact Adj.ne h_adj
  have h_diff_sym2 : (f₁ : Sym2 V) ≠ (f₂ : Sym2 V) := by intro h' ; exact h_diff (Subtype.coe_inj.mp h' )

  by_cases h_1e : (f₁ :Sym2 V) = e

  · -- f₁ = e ≠ f₂
    exact h_e_f f₁ f₂ h_1e h_adj
  · -- e ≠ f₁
    by_cases h_2e : (f₂ :Sym2 V) = e
    · -- f₂ = e ≠ f₁ symmetric to the case above.
      exact (h_e_f f₂ f₁ h_2e h_adj.symm).symm
    · -- f₂ ≠  e ≠ f₁
      have h_1G_S : (f₁ :Sym2 V) ∈ (edgeSet G_S) := by rw [ h_set_diff ] ; exact ⟨ f₁.property, h_1e⟩
      have h_2G_S : (f₂ :Sym2 V) ∈ (edgeSet G_S) := by rw [ h_set_diff ] ; exact ⟨ f₂.property, h_2e⟩
      have h_1eval : C_extension_alt f₁ = C_alt ⟨f₁, h_1G_S ⟩  := by dsimp [C_extension_alt] ; simp [h_1e]
      have h_2eval : C_extension_alt f₂ = C_alt ⟨f₂, h_2G_S ⟩  := by dsimp [C_extension_alt] ; simp [h_2e]
      intro h_same_color
      rw [ h_2eval, h_1eval ] at h_same_color
      dsimp [C_alt ] at h_same_color
      have h_adj_G_S : (lineGraph G_S).Adj ⟨f₁, h_1G_S ⟩ ⟨f₂, h_2G_S ⟩ := by
        rw [Adj, lineGraph ] at *
        simp only at *
        unfold Adjacent at *
        obtain ⟨ z, hz ⟩ := h_adj.left
        rw [ AdjacentAt  ] at hz

        constructor
        · use z
          rw [AdjacentAt]
          exact hz
        · intro h
          have h_fst_eq : (⟨f₁, h_1G_S⟩ : { x // x ∈ G_S.edgeSet }).val = (⟨f₂, h_2G_S⟩ : { x // x ∈ G_S.edgeSet }).val := congr_arg Subtype.val h
          simp only [Subtype.val] at h_fst_eq
          exact h_diff_sym2 h_fst_eq
      have h_C_different : C ⟨f₁, h_1G_S ⟩ ≠ C ⟨f₂, h_2G_S ⟩ := by
        exact Adj.ne (hC h_adj_G_S)

      split_ifs at h_same_color
      with trail_f1 C_f1_α trail_f2_neg f2_α f2_β_neg C_f1_β trail_f2_neg f2_α_neg f2_β _ _ _ trail_f2 f2_α_neg f2_β
      · rw [<- f2_α  ] at C_f1_α
        exact h_C_different C_f1_α
      · exact h_ab h_same_color.symm
      · exact f2_β_neg h_same_color.symm
      · --f₁ reachable with α implies f₂ reachable extending with β
        have f_2_reachable : E_y ⟨ f₂, h_2G_S ⟩  := by
          apply extend_reachable G_S y ⟨ f₁, h_1G_S ⟩ ⟨ f₂, h_2G_S ⟩ h_adj_G_S trail_f1 α β C_f1_α h_same_color.symm
          repeat simp
          exact h_ab
          exact h_yβ

        exact trail_f2_neg f_2_reachable
      · exact h_ab h_same_color
      · rw [<- f2_β ] at C_f1_β
        exact h_C_different C_f1_β
      · exact f2_α_neg h_same_color.symm
      · --f₁ reachable with β implies f₂ reachable extending with α
        have f_2_reachable : E_y ⟨ f₂, h_2G_S ⟩  := by
          apply extend_reachable G_S y ⟨ f₁, h_1G_S ⟩ ⟨ f₂, h_2G_S ⟩ h_adj_G_S trail_f1 β α C_f1_β h_same_color.symm
          repeat simp
          apply Ne.elim
          symm
          exact h_ab
          exact h_yβ
        exact trail_f2_neg f_2_reachable

      · exact C_f1_β h_same_color
      · exact C_f1_α h_same_color
      · exact h_C_different h_same_color
      · exact h_C_different h_same_color
      · --f₂ reachable with β implies f₁ reachable extending with α
        have f_1_reachable : E_y ⟨ f₁, h_1G_S ⟩  := by
          apply extend_reachable G_S y ⟨ f₂, h_2G_S ⟩ ⟨ f₁, h_1G_S ⟩ h_adj_G_S.symm trail_f2 α β f2_α_neg h_same_color
          repeat simp
          exact h_ab
          exact h_yβ
        exact trail_f1 f_1_reachable
      · --f₂ reachable with β implies f₁ reachable extending with α
        have f_1_reachable : E_y ⟨ f₁, h_1G_S ⟩  := by
          apply extend_reachable G_S y ⟨ f₂, h_2G_S ⟩ ⟨ f₁, h_1G_S ⟩ h_adj_G_S.symm trail_f2 β α f2_β h_same_color
          repeat simp
          apply Ne.elim
          symm
          exact h_ab
          exact h_yβ
        exact trail_f1 f_1_reachable
      · exact h_C_different h_same_color
      · exact h_C_different h_same_color


-- have h_nodup : seq.Nodup := by
--     induction h_seq with
--     | nil => simp
--     | cons h_adj h_nin h_prev ih =>
--       simp only [List.nodup_cons]
--       simp at ih
--       exact ⟨by assumption, ih⟩
-- simp [<- List.toFinset_card_of_nodup h_nodup, <- (card_of_finset' seq.toFinset)]
-- have h₁ : Fintype.card {v : V | v ∈ seq} = #seq.toFinset := by apply card_of_finset' seq.toFinset ; simp
-- rw [<-h₁]
-- exact set_fintype_card_le_univ {v | v ∈ seq}


inductive fan_seq_prop {V : Type} {G : SimpleGraph V} {n : ℕ}
(C : EdgeColoring G (Fin n)) (x y₀ : V) : List V → Prop where
  | nil: fan_seq_prop C x y₀ [y₀]
  | cons: ∀ {z : V}, {h_adj : G.Adj x z}
  → C ⟨s(x, z), h_adj ⟩ ∉ C '' edgeSpan G y_i
  → z ∉ y_i :: as
  → fan_seq_prop C x y₀ (y_i :: as)
  → fan_seq_prop C x y₀ (z :: y_i :: as)

def validFanSeqs {V : Type} {G : SimpleGraph V} {n : ℕ}
(C : EdgeColoring G (Fin n)) (x y₀ : V) : Type := {seq : List V // fan_seq_prop C x y₀ seq }

lemma validFanSeqs_length {V : Type} [Fintype V] {G : SimpleGraph V} {n : ℕ}
{C : EdgeColoring G (Fin n)} {x y₀ : V} (seq: List V) (h_seq: fan_seq_prop C x y₀ seq)
: seq.length ≤ Fintype.card V := by
have h_nodup : seq.Nodup := by
    induction h_seq with
    | nil => simp
    | cons h_adj h_nin h_prev ih =>
      simp only [List.nodup_cons]
      simp at ih
      exact ⟨by assumption, ih⟩
simp [<- List.toFinset_card_of_nodup h_nodup, <- (card_of_finset' seq.toFinset)]
have h₁ : Fintype.card {v : V | v ∈ seq} = #seq.toFinset := by apply card_of_finset' seq.toFinset ; simp
rw [<-h₁]
exact set_fintype_card_le_univ {v | v ∈ seq}

lemma validFanSeqs_not_nil {V : Type} {G : SimpleGraph V} {n : ℕ}
{C : EdgeColoring G (Fin n)} {x y₀ : V} {seq: List V} (h_seq: fan_seq_prop C x y₀ seq)
: seq ≠ [] := by
apply List.length_pos.mp
refine List.length_pos_iff_exists_mem.mpr ?_
use y₀
induction h_seq with
| nil => simp
| cons a as => simp at * ; apply Or.inr ; assumption

lemma contains_first {V : Type} {G : SimpleGraph V} {n : ℕ}
{C : EdgeColoring G (Fin n)} {x y₀ : V} {seq: List V} (h_seq: fan_seq_prop C x y₀ seq)
:  y₀ ∈ seq := by
induction h_seq with
|nil=> simp
|cons a b as a_ih => simp at * ; exact Or.inr a_ih

lemma list_length_head {V : Type} {G : SimpleGraph V} {n : ℕ}
{C : EdgeColoring G (Fin n)} {x y₀ : V} (seq: List V) (h_seq: fan_seq_prop C x y₀ seq)
(h_length : 2 ≤ seq.length)
: (seq.head (by apply validFanSeqs_not_nil h_seq )) ≠ y₀ := by
cases h_seq with
|nil=> simp at h_length
|cons a b as =>
simp
intro h₁
rw [h₁] at b
exact b (contains_first as)

def validFanSeqs_adj {V : Type} [Fintype V] {G : SimpleGraph V} {n : ℕ}
{C : EdgeColoring G (Fin n)} {x y₀ : V} {seq: List V} (h_seq: fan_seq_prop C x y₀ seq)
: ∀z ∈ seq, z ≠ y₀ → G.Adj x z  := by
induction h_seq with
| nil =>  simp
| cons h_ad as h_prev a_ih =>
intro z hz
cases List.mem_cons.mp hz with
| inl h₁ => rw [h₁] ; intro ; assumption
| inr h₂ => apply a_ih ; assumption

def validFanSeqs_nodup {V : Type} [Fintype V] {G : SimpleGraph V} {n : ℕ}
{C : EdgeColoring G (Fin n)} {x y₀ : V} {seq: List V} (h_seq: fan_seq_prop C x y₀ seq)
: seq.Nodup := by
induction h_seq with
| nil => simp
| cons h_ad as h_prev a_ih => apply Nodup.cons ; repeat assumption

instance fintypeListsLengthLt (V : Type) [Fintype V] (n : ℕ) : Fintype { seq : List V // seq.length < n } := by
  induction n with
  | zero =>     exact ⟨∅, by simp ⟩
  | succ n ih =>
    let A := { seq : List V // seq.length < n }
    let B := { seq : List V // seq.length = n }
    haveI : Fintype B := Fintype.ofEquiv (List.Vector V n) (Equiv.refl _)
    haveI : Fintype (A ⊕ B) :=  by exact instFintypeSum A B
    let toFun : A ⊕ B → { seq : List V // seq.length < n+1 } := fun x => match x with
      | Sum.inl ⟨seq, h⟩ => ⟨seq, Nat.lt_succ_of_le h.le⟩
      | Sum.inr ⟨seq, h⟩ => ⟨seq, by simp [h]⟩
    let invFun : { seq : List V // seq.length < n+1 } → A ⊕ B := fun ⟨seq, h⟩ =>
      if h' : seq.length < n then Sum.inl ⟨seq, h'⟩
      else Sum.inr ⟨seq, by simp at h'; exact Nat.le_antisymm (Nat.le_of_lt_succ h) h' ⟩
    apply Fintype.ofEquiv (A ⊕ B) {
      toFun := toFun
      invFun := invFun
      left_inv := by
        intro x
        cases x with
        | inl y => rcases y with ⟨ _ , hy ⟩ ; simp [toFun, invFun, hy ]
        | inr y => rcases y with ⟨ _ , hy ⟩ ; simp [toFun, invFun, hy ]
      right_inv := by intro x ; simp [toFun , invFun] ; split_ifs with h' ; repeat simp [h']
  }

instance validFanSeqs_fintype_helper {V : Type} [Fintype V] [DecidableEq V]
  : Fintype { seq : List V // seq.length < Fintype.card V + 1 } := fintypeListsLengthLt V (Fintype.card V + 1)

noncomputable instance validFanSeqs_fintype {V : Type} [Fintype V]  {G : SimpleGraph V} {n : ℕ}
{C : EdgeColoring G (Fin n)} {x y₀ : V} : Fintype (validFanSeqs C x y₀) := by
let maxLen := Fintype.card V + 1
let func: (validFanSeqs C x y₀)
→ {seq: List V // seq.length < Fintype.card V + 1} := λ seq
=> ⟨ seq.1, by apply Nat.lt_succ_of_le ; exact validFanSeqs_length seq.1 seq.2 ⟩
apply Fintype.ofInjective func
intro s₁ s₂ h_eq
cases s₁; cases s₂
simp only [Subtype.mk.injEq, func] at h_eq
exact Subtype.eq h_eq

instance validFanSeqs_finite {V : Type} [Fintype V]  {G : SimpleGraph V} {n : ℕ}
{C : EdgeColoring G (Fin n)} {x y₀ : V} : Finite (validFanSeqs C x y₀) := by
apply Fintype.finite
exact validFanSeqs_fintype

instance validFanSeqs_nonempty {V : Type} [DecidableEq V] {G : SimpleGraph V} {n : ℕ}
  (C : EdgeColoring G (Fin n)) (x y₀ : V)
  : Nonempty (validFanSeqs C x y₀) := by use [y₀] ; exact fan_seq_prop.nil

def validFanSeqs_max {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {n : ℕ}
  (C : EdgeColoring G (Fin n)) (x y₀ : V)
  : ∃ seq : (validFanSeqs C x y₀), ∀ w :(validFanSeqs C x y₀), w.1.length ≤ seq.1.length := by
  apply Finite.exists_max

class SubgraphColoring (V : Type) (G : SimpleGraph V) (n : ℕ) where
  ed : Sym2 V
  coloring : (G.deleteEdges {ed}).edgeSet  -> (Fin n)

-- #check Set.Subset

noncomputable def shifted_colorings {V : Type}  {G: SimpleGraph V} {n : ℕ} (x y₀: V)
(C₀: (G.deleteEdges { s(x,y₀) }).edgeSet  -> (Fin n) ) (seq : List V)
(h_subset : ∀z ∈ seq, z ≠ y₀ ->  G.Adj x z)
: List (SubgraphColoring V G n) := by
induction seq with
| nil => exact []
| cons a as a_ih =>
have this : ∀ z ∈ as , z ≠ y₀ -> G.Adj x z := by intro z hz; apply h_subset ; simp at * ; exact Or.inr hz
have list_prev := @a_ih this
cases list_prev with
| nil => exact [ ⟨ s(x,y₀), C₀ ⟩ ]
| cons B BS =>
rcases B with ⟨ e',  C' ⟩
if hp: a = y₀ then exact [ ⟨ s(x,y₀), C₀ ⟩ ]
else
let C_H : (G.deleteEdges {s(x,a)}).edgeSet  -> (Fin n) := fun ⟨ f, hf⟩  =>
if h₁ : f  = e' then
C' ⟨ s(x,a), by
simp [edgeSet_deleteEdges, <-h₁] at * ; push_neg at * ; exact ⟨ h_subset.1 hp , hf.2.symm ⟩ ⟩
else C' ⟨ f, by simp [edgeSet_deleteEdges] at * ; exact ⟨ hf.1, h₁ ⟩  ⟩
exact ⟨ s(x,a), C_H ⟩ :: ⟨ e',  C' ⟩ :: BS

theorem prop_insert_edge {V : Type} [ Fintype V ] [ DecidableEq V ]  :
∀ ⦃e : (Sym2 V)⦄ {S : Finset (Sym2 V)}, e ∉ S → prop_to_use S → prop_to_use (insert e S) := by
intro e S h_eS IH
rw [prop_to_use] at *
let G_S := (fromEdgeSet (toSet S))
let Δ₁ := ( maxDegree G_S ) + 1
change Colorable (lineGraph G_S ) Δ₁ at IH
let G_host := fromEdgeSet (toSet (insert e S))
let Δ_host_1 := ( maxDegree G_host ) + 1
have delta_comp :  Δ₁ ≤ Δ_host_1   := by
  dsimp
  rw [Nat.add_le_add_iff_right]
  exact (insert_back_degrees).left

change Colorable (lineGraph G_host ) Δ_host_1

by_cases h_diag : e.IsDiag
· -- e is diagonal, and eliminated while forming G_host
  have h_loop : G_host = G_S := by simp [G_host, G_S] ; exact @insert_edgeset_diag V _ _ e h_diag (toSet S)
  have h_loop_deg : Δ_host_1 = Δ₁ := by
    simp [Δ_host_1, Δ₁,G_host, G_S]
    apply congr_arg (fun G => maxDegree G)
    exact @insert_edgeset_diag V _ _ e h_diag (toSet S)
  rw [h_loop, h_loop_deg]
  exact IH
· -- e is non-diagonal, and is an edge of G_host
  have he : (e ∈ edgeSet G_host) := by simp [G_host] ; exact h_diag

  have h_set_diff : (edgeSet G_S ) = (G_host.deleteEdges {e}).edgeSet := by
    simp [ deleteEdges ]
    exact insert_edgeset h_eS

  have h_set_union : G_host.edgeSet = (edgeSet G_S ) ∪ {e} := by
    dsimp [ G_S, G_host ]
    exact insert_edgeset_non_diag h_diag

  obtain ⟨ C ⟩ := IH
  have hC : ∀ {a b : ↑(edgeSet G_S)}, Adj (lineGraph G_S) a b → Adj ⊤ (C a) (C b) := by
    intro f₁ f₂ h₁₇
    change Ne (C f₁) (C f₂)
    exact Coloring.valid C h₁₇

  let x :=  e.out.1
  have h_xe : x ∈ e := Sym2.out_fst_mem e
  let y₀ := Sym2.Mem.other h_xe

  have h_ye : y₀ ∈ e := Sym2.other_mem h_xe
  have h_xy : y₀ ≠ x := Sym2.other_ne h_diag h_xe
  have h_exy : e = s(x,y₀) := (Sym2.mem_and_mem_iff h_xy.symm).mp ⟨ h_xe, h_ye ⟩
  have func: (G_host.deleteEdges {s(x,y₀)}).edgeSet → Fin Δ₁ := by
    simp [<-h_exy,<- h_set_diff]
    use C

  obtain ⟨ seq, h_max ⟩ := validFanSeqs_max C x y₀
  rcases seq with ⟨ seq_1, h_seq ⟩
  let y_last := seq_1.head (by apply validFanSeqs_not_nil h_seq )

  obtain ⟨α,h_α⟩ := missing_color G_S C x
  obtain ⟨β₀,h_β₀⟩ := missing_color G_S C y₀

  by_cases h_xβ: β₀ ∈ C '' edgeSpan G_S x
  · obtain ⟨ f , hf ⟩ := h_xβ
    obtain ⟨ z₁, hz ⟩ := hf.1
    have h_at_least : fan_seq_prop C x y₀ (z₁ :: [y₀]) := by
      apply fan_seq_prop.cons
      simp only [<-hz, hf.2]
      exact h_β₀
      simp
      intro h
      have h_contra: β₀ ∈ C '' edgeSpan G_S y₀ := by
        use f
        exact ⟨ by change y₀ ∈ (f:Sym2 V) ; simp [<-h, hz], hf.2 ⟩
      contradiction
      exact fan_seq_prop.nil
      exact adj_of_edge hz.symm
    specialize h_max ⟨ (z₁ :: [y₀]), h_at_least⟩
    simp at h_max
    have h_adj_seq : ∀ z ∈ seq_1, z ≠ y₀ -> G_host.Adj x z := by
      simp [<-mem_edgeSet]
      intro z hz₁ hz₂
      simp [h_set_union]
      apply Or.inr
      apply validFanSeqs_adj h_seq z hz₁ hz₂
    have color_seq : List (SubgraphColoring V G_host Δ₁) := shifted_colorings x y₀ func seq_1 h_adj_seq

    sorry

  · apply Colorable.mono delta_comp
    apply extending_missing_same h_eS β₀ h_exy h_xβ h_β₀



lemma line_G_colorable_induced {V : Type}  {G : SimpleGraph V}
[ DecidableRel G.Adj] [ h₁ : Fintype V] [h₂ : DecidableEq V]
: prop_to_use (G.edgeSet).toFinset := by
apply Finset.induction_on
· exact empty_graph_easy
· intros e S h_eS h₃
  exact @prop_insert_edge V h₁ h₂ e S h_eS h₃


lemma line_G_colorable [DecidableRel G.Adj] : Colorable (lineGraph G) (maxDegree G + 1)  := by
have h: (prop_to_use (G.edgeSet).toFinset) := by apply line_G_colorable_induced
rw [prop_to_use] at h
simp at h
rw [Set.coe_toFinset, fromEdgeSet_edgeSet] at h
exact h

lemma maxDegree_le_edgeChromaticNumber_rudi (a: Nat) (b: ENat) (h_b : b ≠ ⊤) (h_ab : a ≤ b) : (a ≤ ENat.toNat b) := by
  rcases ENat.ne_top_iff_exists.mp h_b with ⟨m, rfl⟩
  rw [ENat.toNat_coe]
  simp at h_ab
  exact h_ab

theorem maxDegree_le_edgeChromaticNumber  [DecidableRel G.Adj] :
   (maxDegree G) ≤ ENat.toNat ( edgeChromaticNumber G ):= by
  apply maxDegree_le_of_forall_degree_le
  intro v
  apply maxDegree_le_edgeChromaticNumber_rudi (G.degree v) ( edgeChromaticNumber G )
  · apply chromaticNumber_ne_top_iff_exists.mpr
    let n:= Fintype.card (edgeSet G)
    have h : (lineGraph G).Colorable n := by
      apply colorable_of_fintype (lineGraph G)
    exact ⟨n, h⟩
  · exact degree_le_edgeChromaticNumber G v

theorem edgeChromaticNumber_le_succ_maxDegree [DecidableRel G.Adj]  :
edgeChromaticNumber G ≤ maxDegree G + 1 := by
  apply chromaticNumber_le_iff_colorable.mpr
  simp
  exact line_G_colorable G

-- TO DO
-- use Mem.other' to obtain y constructively.
-- show that Mem.other' e ≠ x
