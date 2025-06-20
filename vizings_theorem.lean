import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Walk
import Mathlib.Tactic
import Mathlib.Data.Fintype.Basic

universe v w

open SimpleGraph Hom Iso Embedding Classical

variable {V : Type} {G : SimpleGraph V} {v : V} {α : Type v}

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
-- set_option diagnostics true

theorem AdjacentAt.symm {v : V} {e₁ e₂ : edgeSet G} (h : AdjacentAt v e₁ e₂) : AdjacentAt v e₂ e₁ := ⟨h.right, h.left⟩

def Adjacent (e₁ e₂ : edgeSet G) : Prop := ∃ v, AdjacentAt v e₁ e₂


def lineGraph (G : SimpleGraph V) : SimpleGraph (edgeSet G) where
  Adj := fun e₁ e₂ => Adjacent e₁ e₂ ∧ e₁ ≠ e₂
  symm := by intro e₁ e₂ h ; obtain ⟨w,h'⟩ := h.left ; exact ⟨ ⟨w, AdjacentAt.symm h'⟩, h.right.symm ⟩

variable (G :  SimpleGraph V)

abbrev EdgeColoring (α : Type v) := Coloring (lineGraph G) α

theorem EdgeColoring.valid {α : Type v} {G : SimpleGraph V}
    (c : EdgeColoring G α) {e₁ e₂ : edgeSet G} (h : e₁ ≠ e₂)
    (adj : Adjacent e₁ e₂ ) : c e₁ ≠ c e₂ :=
  Coloring.valid c ⟨adj,h⟩

noncomputable def edgeChromaticNumber : ENat := chromaticNumber (lineGraph G)

variable (v : V) {n:ℕ}

open Fintype Finset

def edgeSpan : Set (edgeSet G) := fun e => Sym2.Mem v e
def neighborSettoEdge (v' : neighborSet G v) : Sym2 V := s(v,v')

theorem other_not_eq_given {x y : V} (hne : x ≠ y)(h₁ : x ∈ s(x,y)) : (Sym2.Mem.other h₁) = y := by
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
    refine ⟨⟨  s(v,v') ,hv'⟩,?_⟩
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

lemma reverse_not_nil {V : Type} {G : SimpleGraph V} {u v : V} (p : G.Walk u v)
    :  ¬ p.Nil -> ¬ p.reverse.Nil := by
    intro h₁ h₂
    rw [ Walk.nil_iff_length_eq, Walk.length_reverse ] at *
    exact h₁ h₂

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
{p : G.Walk v w} {h_nil : ¬ p.Nil}: p.reverse.snd = (Walk.cons h_adj p).reverse.snd := by
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

lemma insert_edgeset_non_diag { V : Type } [ Fintype V] [ DecidableEq V] (e : (Sym2 V)) (h_e_not_diag : ¬ e.IsDiag)
 {S : Finset (Sym2 V)} : edgeSet (fromEdgeSet ((insert e S).toSet)) = (edgeSet (fromEdgeSet S.toSet)) ∪ {e}:= by
simp
ext f
constructor
· simp ; intro hS hf ; exact hS.imp_right (And.intro · hf)
· simp ; intro hS; exact ⟨ hS.imp (id) (And.left), hS.elim (· ▸ h_e_not_diag) And.right⟩
--unused so far

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

instance : IsEmpty (edgeSet (fromEdgeSet ( ∅ : Set (Sym2 V)))) := by
rw [fromEdgeSet_empty]
simp


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

variable [ Fintype V]

lemma empty_zero_max_degree : maxDegree (⊥ : SimpleGraph V) = 0 := by
apply Nat.le_antisymm
· apply maxDegree_le_of_forall_degree_le
  intro v
  have h: degree ⊥ v = 0 := bot_degree v
  exact Nat.le_zero.mpr h
· exact Nat.zero_le (maxDegree ⊥)


lemma subset_card_ne_implies_nonempty_diff [DecidableEq α] {s t : Set α} [Fintype s] [Fintype t]
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

--Given a graph G, a vertex u ∈ V(G), and a function C: E(G) → (Δ+1), then we obtain a proof that there is at least one color missing in the neighbourhood of u
def missing_color (G : SimpleGraph V) [DecidableRel G.Adj] (C : (edgeSet G) → (Fin ( G.maxDegree + 1))) (u : V):  Nonempty (Set.diff (@Set.univ (Fin ( G.maxDegree + 1))) (C '' (edgeSpan G u))) := by
have h_sub : ( (C '' (edgeSpan G u)).toFinset) ⊆ ((@Set.univ (Fin ( G.maxDegree + 1))).toFinset):= by simp
have hcard : 0 < ((@Set.univ (Fin ( G.maxDegree  + 1))).toFinset).card - ((C '' (edgeSpan G u)).toFinset).card := by
  simp
  rw [Nat.lt_succ_iff]
  trans Finset.card (Set.toFinset (edgeSpan G u))
  · exact card_image_le
  · rw [degree_eq_card_edgeSpan]
    exact degree_le_maxDegree G u
exact subset_card_ne_implies_nonempty_diff h_sub hcard

-- if x is adjacent to y₁ and y₂, then C colors the edges xy₁ and xy₂ differently
lemma same_color_impossible (V : Type) (G : SimpleGraph V) (n : ℕ) (C: EdgeColoring G (Fin n))
  { x y₁ y₂ : V} (h₁ : G.Adj x y₁) (h₂ : G.Adj x y₂)
    (h_neq : y₁ ≠ y₂): C ⟨ s(x,y₁), by rw [mem_edgeSet]; exact h₁ ⟩ ≠ C ( ⟨ s(x,y₂), by rw [mem_edgeSet]; exact h₂ ⟩ : edgeSet G ) := by
  apply Coloring.valid
  simp [lineGraph ]
  constructor
  · simp [Adjacent]
    use x
    simp [AdjacentAt]
  · exact ⟨ h_neq, by intro ; apply ne_of_adj G h₁.symm ⟩

def walk_terminal_tail {V : Type} {G : SimpleGraph V} {v u : V} (p : G.Walk v u)
: G.Walk v p.reverse.snd := p.reverse.tail.reverse

inductive at_prop {V : Type} {G : SimpleGraph V} {n:ℕ} {C : EdgeColoring G (Fin n)} { α β : Fin n }
  : ∀ { v u : V }, G.Walk v u → Prop where
  | nil : ∀ {v : V}, at_prop (Walk.nil : G.Walk v v)
  | ba : ∀ {u₂ u₁ v : V}, (p : G.Walk u₁ v) -> (h_prev : @at_prop V G n C α β u₁ v p)
   -> (h_adj : G.Adj u₂ u₁) -> C ⟨ s(u₂, u₁), by rw [mem_edgeSet]; exact h_adj ⟩  = α
   -> (h_norepeat : u₂ ∉ p.support) -> at_prop (Walk.cons h_adj p)
  | ab : ∀ {u₂ u₁ v : V}, (p : G.Walk u₁ v) -> (h_prev : @at_prop V G n C α β u₁ v p )
  -> (h_adj : G.Adj u₂ u₁) -> {hp : ¬ p.Nil } -> C ⟨ s(u₂, u₁), by rw [mem_edgeSet]; exact h_adj ⟩  = β
  -> (h_norepeat : u₂ ∉ p.support) -> at_prop (Walk.cons h_adj p)

lemma at_prop_path {V : Type} {G : SimpleGraph V} {n:ℕ} {C : EdgeColoring G (Fin n)} { α β : Fin n}
{v u: V} {p : G.Walk v u} {h_at_prop: @at_prop _ _ _ C α β _ _ p } :
p.IsPath := by
induction h_at_prop with
  | nil => exact Walk.IsPath.nil
  | ba _ _ _  _ h_norepeat ih =>
    exact Walk.IsPath.cons ih h_norepeat
  | ab _ _ _ _ h_norepeat ih =>
    exact Walk.IsPath.cons ih h_norepeat

class alt_path {V : Type} {G : SimpleGraph V} {n : ℕ} {C : EdgeColoring G (Fin n)}
{ α β : Fin n} {v u : V}  where
  walk : G.Walk v u
  alternating_property : @at_prop V G n C α β v u walk

lemma copy_at_prop {V : Type} {G : SimpleGraph V} {v u v' u': V} {n:ℕ} {C : EdgeColoring G (Fin n)}
{ α β : Fin n} { p : G.Walk v u } { h₁ : v = v' } { h₂ : u = u' } :
 @at_prop _ _ _  C β α _ _  p ↔ @at_prop  _ _ _ C β α _ _ (Walk.copy p h₁ h₂)
:= by cases h₁ ; cases h₂ ; simp at *

lemma at_prop_cons_term_tail {V : Type} {G : SimpleGraph V} {n:ℕ} {C : EdgeColoring G (Fin n)} { α β : Fin n}
 {v₁ v₂ u: V} {h_adj : G.Adj v₂ v₁} {p : G.Walk v₁ u}
{h_at_prop: @at_prop _ _ _ C α β _ _ (Walk.cons h_adj (walk_terminal_tail p))} :
 @at_prop _ _ _ C α β _ _ (walk_terminal_tail ( Walk.cons h_adj p )) := by
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
    apply same_color_impossible V G n C h_adj.symm h_adj₂
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

lemma terminal_tail_concat {V : Type} {G : SimpleGraph V} {v u₁ u₂ : V} {C : EdgeColoring G (Fin n)} { α β : Fin n}
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


lemma concat_terminal_tail {V : Type} {G : SimpleGraph V} {v u : V}
{p : G.Walk v u} {h_adj : G.Adj p.reverse.snd u} {h_nil : ¬ p.Nil}
: (walk_terminal_tail p).concat h_adj =  p := by
induction p with
| nil=> simp at *
| cons =>

sorry


lemma next_vertex_unique {V : Type} {G : SimpleGraph V} {n : ℕ} {C: EdgeColoring G (Fin n)}
  {α β : Fin n} {x y : V} {color : Fin n}
  {z₁ z₂ : V} {w₁ : G.Walk z₁ y} {w₂ : G.Walk z₂ y}
  (h₁ : G.Adj x z₁) (h₂ : G.Adj x z₂)
  (hc₁ : C ⟨s(x, z₁), by rw [mem_edgeSet]; exact h₁⟩ = color)
  (hc₂ : C ⟨s(x, z₂), by rw [mem_edgeSet]; exact h₂⟩ = color)
  (hat₁ : @at_prop V G n C α β z₁ y w₁) (hat₂ : @at_prop V G n C α β z₂ y w₂)
  : z₁ = z₂ := sorry

lemma rev_adj_snd {V : Type} {G : SimpleGraph V} {v u : V} {p : G.Walk v u} (hp : ¬ p.Nil) :
    G.Adj u p.reverse.snd:= by
    apply @Walk.adj_snd V G u v p.reverse
    apply reverse_not_nil
    assumption


lemma color_first_dart {V : Type} {G : SimpleGraph V} {n : ℕ} {C: EdgeColoring G (Fin n)}
  { α β : Fin n } {v u : V} {p: G.Walk v u} {h_nil : ¬ p.Nil} (h : @at_prop V G n C α β v u p )
  : C ⟨s( p.reverse.snd, u), (rev_adj_snd h_nil).symm ⟩ = α := by sorry



lemma alt_path_reverse_snd_unique {V : Type} {G : SimpleGraph V} {n : ℕ} {C: EdgeColoring G (Fin n)}
  { α β : Fin n} {v u : V} {w₁ w₂: G.Walk v u}
  (h₁ : @at_prop _ _ _ C α β v u w₁ ) (h₂ : @at_prop _ _ _ C α β v u w₂)
  : w₁.reverse.snd = w₂.reverse.snd := by

  -- /sorry
  cases w₁ with
  |nil =>
    cases w₂ with
    |nil => simp
    |cons h_adj₂ p₂ =>
      have h_path : (Walk.cons h_adj₂ p₂).Nil := by
        rw [Walk.nil_iff_eq_nil]
        rw [ <-Walk.isPath_iff_eq_nil]
        apply at_prop_path
        assumption
      simp at h_path

  |cons h_adj₁ p₁ =>
    cases p₁ with
    |nil =>
      cases w₂ with
        |nil => simp

        |cons h_adj₂ p₂ =>
          let w₁' := (Walk.cons h_adj₁ Walk.nil)
          let w₂' := (Walk.cons h_adj₂ p₂)
          change w₁'.reverse.snd = w₂'.reverse.snd
          have h_nil₁ : ¬ w₁'.Nil := by simp [w₁']
          have h_nil₂ : ¬ w₂'.Nil := by simp [w₂']
          have h_u1 : G.Adj u w₁'.reverse.snd := rev_adj_snd h_nil₁
          have h_u2 : G.Adj u w₂'.reverse.snd := rev_adj_snd h_nil₂
          
          sorry

    |cons => sorry



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
  |cons a b =>
  simp [motive] at a_ih
  let tail₁ := walk_terminal_tail (w₁'.concat h_adj)
  let tail₂ := walk_terminal_tail (Walk.cons a b)
  have h₁_tail := terminal_tail_at_prop h₁
  have h₂_tail := terminal_tail_at_prop h₂
  change at_prop tail₁ at h₁_tail
  change at_prop tail₂ at h₂_tail
  have h_rev_snd : (w₁'.concat h_adj).reverse.snd = z  := by simp
  have h_rev_snd_2 : (Walk.cons a b).reverse.snd = z  := by
    rw [<-h_rev_snd]
    apply alt_path_reverse_snd_unique
    repeat assumption
  have h₁_tail_copy : @at_prop _ _ _ C β α _ _ (Walk.copy tail₁ rfl h_rev_snd) := by apply copy_at_prop.mp; apply h₁_tail
  have h₂_tail_copy : @at_prop _ _ _ C β α _ _ (Walk.copy tail₂ rfl h_rev_snd_2) := by apply copy_at_prop.mp; apply h₂_tail
  have h_p1 : @at_prop _ _ _ C β α _ _ w₁' := @terminal_tail_concat _ _ _ _ _ _ _ _ _ _ _ h₁_tail_copy
  specialize a_ih β α h_p1 (Walk.copy tail₂ rfl h_rev_snd_2) h₂_tail_copy
  simp [a_ih, tail₂]
  simp [Walk.copy ]
  cases h_rev_snd_2
  simp
  apply concat_terminal_tail
  simp
repeat assumption



def R_reach {V : Type} {G : SimpleGraph V} {n: ℕ}
 {C: EdgeColoring G (Fin n)} {α β : Fin n} {v: V}
: V → Prop := fun z => Nonempty (@alt_path V G n C α β v z)

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

noncomputable instance induced_decidable {V : Type} [ Fintype V] [ DecidableEq V] {S : Finset (Sym2 V)}
: DecidableRel ( (fromEdgeSet (toSet S)).Adj ) := by exact Classical.decRel ((fromEdgeSet (toSet S)).Adj)

theorem prop_insert_edge {V : Type} [  Fintype V] [ DecidableEq V] {G : SimpleGraph V} [ DecidableRel G.Adj]  :
∀ ⦃e : (Sym2 V)⦄ {S : Finset (Sym2 V)}, e ∉ S → prop_to_use S → prop_to_use (insert e S) := by
intro e S h_eS IH
rw [prop_to_use] at *
let G_S := (fromEdgeSet (toSet S))
let Δ₁ := ( maxDegree G_S ) + 1
change Colorable (lineGraph G_S ) Δ₁ at IH
let G_host := fromEdgeSet (toSet (insert e S))
let Δ_host_1 := ( maxDegree G_host ) + 1
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
  have h_set_diff : (edgeSet G_S )  = edgeSet G_host \ ( {e} : Set (Sym2 V) ) := by
    dsimp
    exact insert_edgeset h_eS
  obtain ⟨ C ⟩ := IH
  have hC : ∀ {a b : ↑(edgeSet G_S)}, Adj (lineGraph G_S) a b → Adj ⊤ (C a) (C b) := by
    intro f₁ f₂ h₁₇
    change Ne (C f₁) (C f₂)
    exact Coloring.valid C h₁₇
  let x :=  e.out.1
  have h_xe : x ∈ e := Sym2.out_fst_mem e
  let y := Sym2.Mem.other h_xe
  have h_ye : y ∈ e := Sym2.other_mem h_xe
  have h_xy : y ≠ x := Sym2.other_ne h_diag h_xe
  have h_exy : e = s(x,y) := (Sym2.mem_and_mem_iff h_xy.symm).mp ⟨ h_xe, h_ye ⟩
  obtain ⟨alpha,h_alpha⟩ := missing_color (fromEdgeSet (toSet S)) C x
  obtain ⟨beta,h_beta⟩ := missing_color (fromEdgeSet (toSet S)) C y
  have delta_comp :  Δ₁ ≤ Δ_host_1   := by
    dsimp
    rw [Nat.add_le_add_iff_right]
    exact (insert_back_degrees).left
  by_cases h_ab : alpha = beta
  · -- Assume alpha = beta is missing in both x and y
    apply Colorable.mono delta_comp
    let C_extension_alt : edgeSet G_host → (Fin Δ₁) := fun f =>
    if h_ef: f = e then alpha else
    have h_f : f.val ∈ (edgeSet G_S) := by
      have h_f_host : f.val  ∈ edgeSet G_host := f.property
      rw [ h_set_diff ]
      exact ⟨h_f_host, h_ef⟩
    (C ⟨ f, h_f ⟩)
    use C_extension_alt
    intro f₁ f₂ h_adj
    change Ne (C_extension_alt f₁) (C_extension_alt f₂)
    intro h_same_color
    have h_diff : f₁ ≠ f₂ := by exact Adj.ne h_adj
    have h_diff_sym2 : (f₁ :Sym2 V) ≠ (f₂ :Sym2 V) := by intro h' ; exact h_diff (Subtype.coe_inj.mp h' )

    have symmetric_argument_f12 (f₁ f₂ : edgeSet G_host ) (h_1e : (f₁ : Sym2 V) = e) (h_diff_sym2 : (f₁ : Sym2 V) ≠ (f₂ : Sym2 V) )
      (h_same_color : C_extension_alt f₁ = C_extension_alt f₂)
      (h_adj : Adj (lineGraph G_host) f₁ f₂) : False := by
      have h_1eval : C_extension_alt f₁ = alpha  := by dsimp [C_extension_alt] ; simp [h_1e]
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
      have touching_e_impossible (γ : Fin Δ₁ ) (h_γαβ : γ = alpha ∨ γ = beta) (u z : V)
      (h_gamma : γ ∈  Set.diff (@Set.univ (Fin Δ₁)) (C '' (edgeSpan G_S u)) )
      (h_zu :  z = u ) (hz_e :  Sym2.Mem z e ) ( hz_f₂ : Sym2.Mem z f₂ ) : False := by
        have h_same_color_γ : γ = C { val := ↑f₂, property := h_2G_S } := by
          cases h_γαβ with
          | inl h_γα => rw [← h_γα] at h_same_color ; exact h_same_color
          | inr h_γβ => rw [← h_ab ] at h_γβ ; rw [← h_γβ ] at h_same_color ; exact h_same_color

        have h_f2_span_u :  ⟨ f₂, h_2G_S ⟩ ∈ (edgeSpan G_S u) := by rw [← h_zu] ; exact hz_f₂
        have h_gamma_in_image : γ ∈ C '' edgeSpan G_S u := by use ⟨ f₂, h_2G_S ⟩ ; exact ⟨ h_f2_span_u , h_same_color_γ.symm ⟩
        rw [Set.diff] at h_gamma
        dsimp at h_gamma
        exact h_gamma.right h_gamma_in_image

      cases h_zxy with
      | inl h_zx  =>
      exact touching_e_impossible alpha (Or.inl rfl) x z h_alpha h_zx  hz_e hz_f₂
      | inr h_zy =>
      exact touching_e_impossible beta (Or.inr rfl) y z h_beta h_zy hz_e hz_f₂

    by_cases h_1e : (f₁ :Sym2 V) = e
    · exact symmetric_argument_f12 f₁ f₂ h_1e h_diff_sym2 h_same_color h_adj
    · by_cases h_2e : (f₂ :Sym2 V) = e
      · exact symmetric_argument_f12 f₂ f₁ h_2e h_diff_sym2.symm h_same_color.symm h_adj.symm
      · have h_1G_S : (f₁ :Sym2 V) ∈ (edgeSet G_S) := by rw [ h_set_diff ] ; exact ⟨ f₁.property, h_1e⟩
        have h_2G_S : (f₂ :Sym2 V) ∈ (edgeSet G_S) := by rw [ h_set_diff ] ; exact ⟨ f₂.property, h_2e⟩
        have h_12eval : C ⟨f₁, h_1G_S ⟩ = C ⟨f₂, h_2G_S ⟩  := by dsimp [C_extension_alt] at h_same_color ; simp [h_1e, h_2e] at h_same_color ; exact h_same_color
        have adjacent_line_G_S : Adj (lineGraph G_S) ⟨f₁, h_1G_S ⟩ ⟨f₂, h_2G_S ⟩ := by
          -- rw [Adj, lineGraph ] at *
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
  let R_y : V → Prop := fun z => @R_reach V G_S Δ₁ C alpha beta y z
  · -- alpha ≠ beta
    by_cases hp : @R_reach V G_S Δ₁ C alpha beta y x
    · -- tough part
      sorry
    · -- if there is no alternating path from y to x, then we can color with only Δ_host_1 colors, not needing an extra color.
      -- this is done by interchanging alpha and beta in the paths originating from y and coloring e by alpha
      apply Colorable.mono delta_comp
      let E_y : edgeSet G_S → Prop := fun f => ∃ ℓ₁ ℓ₂, ( s(ℓ₁,ℓ₂) = (f: Sym2 V) ∧ R_y ℓ₁ ∧ R_y ℓ₂)
      let C_alt : (edgeSet G_S → (Fin Δ₁)) := fun f =>
        if E_y f then
          if C f = alpha then beta
          else if C f = beta then alpha
          else C f
        else C f

      let C_extension_alt : edgeSet G_host → (Fin Δ₁) := fun f =>
      if h_ef: f = e then alpha
      else
      have h_f : f.val ∈ (edgeSet G_S) := by
        have h_f_host : f.val  ∈ edgeSet G_host := f.property
        rw [ h_set_diff ]
        exact ⟨h_f_host, h_ef⟩
      C_alt ⟨ f, h_f ⟩

      use C_extension_alt
      intro f₁ f₂ h_adj
      change Ne (C_extension_alt f₁) (C_extension_alt f₂)
      by_contra h_same_color
      have h_diff : f₁ ≠ f₂ := by exact Adj.ne h_adj
      have h_diff_sym2 : (f₁ :Sym2 V) ≠ (f₂ :Sym2 V) := by intro h' ; exact h_diff (Subtype.coe_inj.mp h' )

      by_cases h_1e : (f₁ :Sym2 V) = e
      · -- f₁ = e ≠ f₂
        have h_1eval : C_extension_alt f₁ = alpha  := by dsimp [C_extension_alt] ; simp [h_1e]
        have h_2e : (f₂ :Sym2 V) ≠ e := by rw [h_1e] at h_diff_sym2 ; exact Ne.symm h_diff_sym2
        have h_2G_S : (f₂ :Sym2 V) ∈ (edgeSet G_S) := by rw [ h_set_diff ] ; exact ⟨ f₂.property, h_2e⟩
        have h_2eval : C_extension_alt f₂ = C_alt ⟨f₂, h_2G_S ⟩  := by dsimp [C_extension_alt] ; simp [h_2e]
        rw [ h_2eval, h_1eval ] at h_same_color
        dsimp [C_alt ] at h_same_color

        have touching_e_impossible_beta ( hz_f₂ : Sym2.Mem y f₂ )
        (change_β_2_α : C { val := ↑f₂, property := h_2G_S } = beta  )
        : False := by
          have h_f2_span_y :  ⟨ f₂, h_2G_S ⟩ ∈ (edgeSpan G_S y) := by exact hz_f₂
          have h_beta_in_image : beta ∈ C '' edgeSpan G_S y := by use ⟨ f₂, h_2G_S ⟩
          rw [Set.diff] at h_beta
          dsimp at h_beta
          exact h_beta.right h_beta_in_image

        have touching_e_impossible_alpha ( hz_f₂ : Sym2.Mem x f₂ )
        (colored_alpha : alpha = C { val := ↑f₂, property := h_2G_S } )
        : False := by
          have h_f2_span_x :  ⟨ f₂, h_2G_S ⟩ ∈ (edgeSpan G_S x) := by exact hz_f₂
          have h_alpha_in_image : alpha ∈ C '' edgeSpan G_S x := by use ⟨ f₂, h_2G_S ⟩ ; exact ⟨ h_f2_span_x , colored_alpha.symm ⟩
          rw [Set.diff] at h_alpha
          dsimp at h_alpha
          exact h_alpha.right h_alpha_in_image

        rw [Adj, lineGraph] at h_adj
        simp only at h_adj
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
            rcases exists_trail with ⟨v₁, v₂, h_f₂, trail₁, trail₂⟩
            have h_x_mem : x = v₁ ∨ x = v₂ := by rw [ h_zx, ← h_f₂, Sym2.mem_iff'] at hz_f₂ ; exact hz_f₂
            have yx_trail: (R_y x) := by
              cases h_x_mem with
              | inl h_x_v₁ => rw [h_x_v₁]  ; exact trail₁
              | inr h_x_v₂ => rw [h_x_v₂]  ; exact trail₂
            exact hp yx_trail
          | inr  h_zy =>
            rw [ h_zy ] at hz_f₂
            exact touching_e_impossible_beta hz_f₂ change_β_2_α
        · -- DONE exists_trail, neither alpha nor beta, no change
          exact change_α_2_β h_same_color.symm
        · -- DONE exists NO trail, no change
          cases h_zxy with
          | inl  h_zx =>
            rw [ h_zx ] at hz_f₂
            exact touching_e_impossible_alpha hz_f₂ h_same_color
          | inr  h_zy =>
            rw [ h_zy ] at hz_f₂
            let other := Sym2.Mem.other hz_f₂
            have h_f₂_eq : s(y, other) = ↑f₂  := by exact Sym2.other_spec hz_f₂
            have nil_trail_y : R_y y := by
              change R_reach y ; use Walk.nil ; exact @at_prop.nil V G_S Δ₁ C alpha beta y
            have reachable : R_y other := by
              change R_reach other
              have h_edge : G_S.Adj other y := by rw [ Sym2.eq_swap ] at h_f₂_eq;  rw [← mem_edgeSet, h_f₂_eq] ; exact h_2G_S
              have h_color : C ⟨ s(y , other ) , by  rw [ h_f₂_eq ] ; exact h_2G_S  ⟩  = alpha := by
                have h_coerce_down : ( ⟨ s(y , other )  , by rw [ h_f₂_eq ] ; exact h_2G_S  ⟩ : edgeSet G_S ) = ( ⟨ f₂, h_2G_S  ⟩  : edgeSet G_S) := sorry
                rw [ h_coerce_down ]
                exact h_same_color.symm
              use Walk.cons h_edge.symm (Walk.nil' other)
              apply @at_prop.ba V G_S Δ₁ C alpha beta
              exact (@at_prop.nil V G_S Δ₁ C alpha beta other)
              exact h_color
              simp
              exact (Adj.ne h_edge).symm

            change R_reach other at reachable
            have h_exists : ∃ ℓ₁ ℓ₂, s(ℓ₁, ℓ₂) = (f₂ : Sym2 V) ∧ R_y ℓ₁ ∧ R_y ℓ₂ := by
              use y, other
            exact exists_trail h_exists
      · -- e ≠ f₁
        by_cases h_2e : (f₂ :Sym2 V) = e
        · -- EASY SYMMETRY f₂ = e ≠ f₁ symmetric to the case above.
          sorry
        · -- f₂ ≠  e ≠ f₁
          have h_1G_S : (f₁ :Sym2 V) ∈ (edgeSet G_S) := by rw [ h_set_diff ] ; exact ⟨ f₁.property, h_1e⟩
          have h_2G_S : (f₂ :Sym2 V) ∈ (edgeSet G_S) := by rw [ h_set_diff ] ; exact ⟨ f₂.property, h_2e⟩
          have h_1eval : C_extension_alt f₁ = C_alt ⟨f₁, h_1G_S ⟩  := by dsimp [C_extension_alt] ; simp [h_1e]
          have h_2eval : C_extension_alt f₂ = C_alt ⟨f₂, h_2G_S ⟩  := by dsimp [C_extension_alt] ; simp [h_2e]
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
          ·
            sorry
          · exact h_ab h_same_color
          · rw [<- f2_β ] at C_f1_β
            exact h_C_different C_f1_β
          · exact f2_α_neg h_same_color.symm
          ·
            have f_2_reachable : E_y ⟨ f₂, h_2G_S ⟩  := by sorry
            exact trail_f2_neg f_2_reachable
          · exact C_f1_β h_same_color
          · exact C_f1_α h_same_color
          · exact h_C_different h_same_color
          · exact h_C_different h_same_color
          ·
            sorry
          ·
            sorry
          · exact h_C_different h_same_color
          · exact h_C_different h_same_color

lemma line_G_colorable_induced {V : Type}  {G : SimpleGraph V} [ DecidableRel G.Adj] [ h₁ : Fintype V] [h₂ : DecidableEq V] : prop_to_use (G.edgeSet).toFinset := by
apply Finset.induction_on
· exact empty_graph_easy
· intros e S h_eS h₃
  exact @prop_insert_edge V h₁ h₂ G _ e S h_eS h₃


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
