import Mathlib.Tactic
import MAT740TopologyInLeanHS25.Definitions.TopologicalSpaces
import MAT740TopologyInLeanHS25.Definitions.Bases


/-
Let Top(X,Y) := {f : X → Y | f continuous} denote the set of continuous maps from X to Y.

We can characterize a topological space X by either by specifying either
- Top(X,T) for all spaces T
- Top(T,X) for all spaces T.

This is a consequence of the Yoneda lemma.
You can also see it directly since id ∈ Top((X,TX),(X,TX')) is equivalent to TX' ⊆ TX.
In other words, the topology on X is completely determined (up to unique homeomorphism) by the continuous maps going into X (resp. out of X).
-/

namespace Constructions

universe u

/- # Subspaces -/
class Subspace (X : Type u) [TX : Topology X] where
  S : Type u
  TS : Topology S
  incl : S → X
  Injective_incl : Function.Injective incl
  /- Top(T,S) ≅ {f : T → S | incl ∘ f : T → X continuous }. -/
  char_Subspace {T : Type u} (TT: Topology T) (f : T → S) : Cont f ↔ Cont (incl ∘ f)

variable {X : Type u} [TX : Topology X] {S : Type u} [TS : Topology S]

theorem Cont_incl [sub : Subspace X] : @Cont sub.S X sub.TS TX (sub.incl) := by
  have h : sub.incl ∘ id = sub.incl := by
    exact rfl
  rw [← h]
  rw [← sub.char_Subspace]
  intro U open_U
  exact open_U

@[simp]
def Coarser (T T' : Topology X) : Prop :=
  @Cont X X T' T id

@[simp]
def Finer (T T' : Topology X) : Prop := @Coarser X T' T

infix:50 " ≤ " => Coarser -- T ≤ T' means T is coarser than T'
infix:50 " ≥ " => Finer

/- The subspace topology is the smallest (coarsest) topology on S that makes `incl` continuous. -/
theorem initial_Subspace [sub : Subspace X] [TS' : Topology sub.S] :
  @Cont sub.S X TS' TX sub.incl → sub.TS ≤ TS' := by
  intro h
  rw [Coarser]
  rw [sub.char_Subspace, Function.comp_id]
  exact h

instance pullbackTopology (X : Type u) (TX : Topology X) (S : Type u) (f : S → X) : Topology S where
  Open := fun (U : Set S) ↦ ∃ (V : Set X), Open V ∧ U = f ⁻¹' V
  Open_univ := by
    use Set.univ; simp
  Open_inter := by
    intro U1 U2 hU1 hU2
    obtain ⟨V1, hV1_open, hV1_pre⟩ := hU1
    obtain ⟨V2, hV2_open, hV2_pre⟩ := hU2
    use V1 ∩ V2
    constructor
    case left => exact Open_inter hV1_open hV2_open
    case right =>
      rw [Set.preimage_inter, hV1_pre, hV2_pre]
  Open_sUnion := by
    intro C hC
    use ⋃₀ {V | Open V ∧ ∃ U ∈ C, U = f ⁻¹' V}
    constructor
    case left =>
      apply Open_sUnion
      intro V hV
      rw [Set.mem_setOf] at hV
      exact hV.left
    case right =>
      ext s
      constructor
      case mp =>
        intro hs
        obtain ⟨A, hA1, hA2⟩:= hs
        simp only [exists_eq_right, Set.preimage_sUnion, Set.mem_setOf_eq, Set.mem_iUnion,
          Set.mem_preimage, exists_prop]
        specialize hC A hA1
        obtain ⟨V, hV1, hV2⟩:= hC
        use V
        rw [← hV2]
        rw [hV2] at hA2
        exact ⟨⟨hV1, hA1⟩, hA2⟩
      case mpr =>
        simp only [exists_eq_right, Set.preimage_sUnion, Set.mem_setOf_eq, Set.mem_iUnion,
          Set.mem_preimage, exists_prop, Set.mem_sUnion, forall_exists_index, and_imp]
        intro V open_V hV1 hV2
        use f ⁻¹' V
        exact ⟨hV1, hV2⟩

instance Subspace_subspaceTopology (incl : S → X) (inj : Function.Injective incl)
  : Subspace X where
    S := S
    TS := pullbackTopology X TX S incl
    incl := incl
    Injective_incl := inj
    char_Subspace := by
      sorry -- exercise

/- # Quotient Spaces -/

class Quotient (X : Type u) [TX : Topology X] where
  Q : Type u
  TQ : Topology Q
  qmap : X → Q
  Surjective_qmap : Function.Surjective qmap
  /- Top(Q,T) ≅ {f : Q → T | f ∘ qmap : X → T continuous }. -/
  char_Quotient {T : Type u} (TT: Topology T) (f : Q → T) : Cont f ↔ Cont (f ∘ qmap)

theorem Cont_qmap [quot : Quotient X] : @Cont X quot.Q TX quot.TQ quot.qmap := by
  sorry -- exercise

/- The quotient topology is the largest (finest) topology on Q that makes `qmap` continuous. -/
theorem final_Quotient [quot : Quotient X] [TQ' : Topology quot.Q] :
  @Cont X quot.Q TX TQ' quot.qmap → TQ' ≤ quot.TQ := by
    sorry -- exercise

instance pushforwardTopology
  (X : Type u) (TX : Topology X) (Q : Type u) (qmap : X → Q)
  : Topology Q where
    Open := fun (U : Set Q) ↦ Open (qmap ⁻¹' U)
    Open_univ := by
      sorry
    Open_inter := by
      sorry
    Open_sUnion := by
      sorry -- hint : Open_preimageUnion

instance Quotient_quotientTopology
  {Q : Type u} (qmap : X → Q) (surj : Function.Surjective qmap)
  : Quotient X where
    Q := Q
    TQ := pushforwardTopology X TX Q qmap
    qmap := qmap
    Surjective_qmap := surj
    char_Quotient := by
      sorry --exercise

end Constructions
