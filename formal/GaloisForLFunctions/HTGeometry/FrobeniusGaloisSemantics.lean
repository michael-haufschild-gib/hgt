import GaloisForLFunctions.HTGeometry.FrobeniusGaloisKalman

/-!
# Positive-cone semantics for arbitrary Frobenius formulas

The concrete powerset/Kalman instance of arXiv:2609.09529,
Proposition 5.7 and Theorems 5.12–5.15. Structural induction transports
all formulas, equations, and arbitrary families of equational premises.
The interpretation in the cone uses its center as bottom and truncates
multiplication at the center, exactly as the positive-cone construction requires.
-/
namespace GaloisForLFunctions.HTGeometry.FrobeniusGalois

/-- Formulas in the expanded residuated-lattice language. -/
inductive Formula (ι : Type*) where
  | atom : ι → Formula ι
  | bottom : Formula ι
  | top : Formula ι
  | meet : Formula ι → Formula ι → Formula ι
  | join : Formula ι → Formula ι → Formula ι
  | tensor : Formula ι → Formula ι → Formula ι
  | residual : Formula ι → Formula ι → Formula ι
  | necessity : Formula ι → Formula ι
  | possibility : Formula ι → Formula ι

namespace Formula
variable {ι X Y : Type*}

/-- Interpretation in the property algebra of an arbitrary observation. -/
def eval (q : X → Y) (v : ι → Set X) : Formula ι → Set X
  | atom i => v i
  | bottom => ∅
  | top => Set.univ
  | meet a b => eval q v a ∩ eval q v b
  | join a b => eval q v a ∪ eval q v b
  | tensor a b => eval q v a ∩ eval q v b
  | residual a b => implication (eval q v a) (eval q v b)
  | necessity a => lower q (eval q v a)
  | possibility a => upper q (eval q v a)

/-- Interpretation with the operations of the positive cone. -/
def evalCone (q : X → Y) (v : ι → Twist X) : Formula ι → Twist X
  | atom i => v i
  | bottom => Twist.center
  | top => Twist.top
  | meet a b => Twist.meet (evalCone q v a) (evalCone q v b)
  | join a b => Twist.join (evalCone q v a) (evalCone q v b)
  | tensor a b => Twist.join (Twist.tensor (evalCone q v a) (evalCone q v b)) Twist.center
  | residual a b => Twist.residual (evalCone q v a) (evalCone q v b)
  | necessity a => Twist.necessity q (evalCone q v a)
  | possibility a => Twist.possibility q (evalCone q v a)

/-- Evaluation commutes with the positive-cone embedding for every formula. -/
theorem evalCone_positive (q : X → Y) (v : ι → Set X) (a : Formula ι) :
    evalCone q (fun i => Twist.positive (v i)) a = Twist.positive (eval q v a) := by
  induction a with
  | atom i => rfl
  | bottom => rfl
  | top => rfl
  | meet a b ha hb =>
      simp only [evalCone, eval, ha, hb, Twist.positive_meet]
  | join a b ha hb =>
      simp only [evalCone, eval, ha, hb, Twist.positive_join]
  | tensor a b ha hb =>
      simp only [evalCone, eval, ha, hb, Twist.positive_tensor]
  | residual a b ha hb =>
      simp only [evalCone, eval, ha, hb, Twist.positive_residual]
  | necessity a ha =>
      simp only [evalCone, eval, ha, Twist.necessity_positive]
  | possibility a ha =>
      simp only [evalCone, eval, ha, Twist.possibility_positive]

/-- The embedding reflects equality. -/
theorem positive_eq_iff (S T : Set X) : Twist.positive S = Twist.positive T ↔ S = T :=
  ⟨fun h => congrArg Twist.pos h, fun h => congrArg Twist.positive h⟩

/-- Formula equations have identical truth in both representations. -/
theorem equation_transport (q : X → Y) (v : ι → Set X) (a b : Formula ι) :
    evalCone q (fun i => Twist.positive (v i)) a =
      evalCone q (fun i => Twist.positive (v i)) b ↔ eval q v a = eval q v b := by
  rw [evalCone_positive, evalCone_positive, positive_eq_iff]

/-- Designated truth is preserved and reflected, including nested unary operators. -/
theorem truth_transport (q : X → Y) (v : ι → Set X) (a : Formula ι) :
    evalCone q (fun i => Twist.positive (v i)) a = Twist.top ↔ eval q v a = Set.univ := by
  rw [evalCone_positive]
  exact positive_eq_iff _ Set.univ

/-- Every positive-cone valuation is accounted for, rather than just chosen embeddings. -/
theorem evalCone_all_positive (q : X → Y)
    (v : ι → {a : Twist X // Twist.center ≤ a}) (a : Formula ι) :
    evalCone q (fun i => (v i).1) a = Twist.positive (eval q (fun i => (v i).1.pos) a) := by
  have hv : (fun i => (v i).1) = (fun i => Twist.positive (v i).1.pos) := by
    funext i
    apply Twist.ext
    · rfl
    · exact (Twist.center_le_iff _).mp (v i).2
  rw [hv]
  exact evalCone_positive q _ a

/-- Equational validity is identical over properties and over the entire positive cone. -/
theorem equation_validity_transport (q : X → Y) (a b : Formula ι) :
    (∀ v : ι → Set X, eval q v a = eval q v b) ↔
      ∀ v : ι → {a : Twist X // Twist.center ≤ a},
        evalCone q (fun i => (v i).1) a = evalCone q (fun i => (v i).1) b := by
  constructor
  · intro h v
    rw [evalCone_all_positive, evalCone_all_positive, h]
  · intro h v
    let w : ι → {a : Twist X // Twist.center ≤ a} := fun i => Twist.positiveConeEquiv (v i)
    exact (equation_transport q v a b).mp (h w)

/-- Arbitrary equational premises, including finite quasi-equations, transport exactly. -/
theorem equational_consequence_transport (q : X → Y)
    (Γ : Set (Formula ι × Formula ι)) (a b : Formula ι) :
    (∀ v : ι → Set X,
      (∀ p ∈ Γ, eval q v p.1 = eval q v p.2) → eval q v a = eval q v b) ↔
    (∀ v : ι → {a : Twist X // Twist.center ≤ a},
      (∀ p ∈ Γ, evalCone q (fun i => (v i).1) p.1 =
        evalCone q (fun i => (v i).1) p.2) →
      evalCone q (fun i => (v i).1) a = evalCone q (fun i => (v i).1) b) := by
  constructor
  · intro h v hv
    rw [evalCone_all_positive, evalCone_all_positive, positive_eq_iff]
    apply h
    intro p hp
    have he := hv p hp
    rw [evalCone_all_positive, evalCone_all_positive, positive_eq_iff] at he
    exact he
  · intro h v hv
    let w : ι → {a : Twist X // Twist.center ≤ a} := fun i => Twist.positiveConeEquiv (v i)
    apply (equation_transport q v a b).mp
    apply h w
    intro p hp
    exact (equation_transport q v p.1 p.2).mpr (hv p hp)

/-- Counterexamples to an equation survive the representation in both directions. -/
theorem countermodel_transport (q : X → Y) (a b : Formula ι) :
    (∃ v : ι → Set X, eval q v a ≠ eval q v b) ↔
      ∃ v : ι → {a : Twist X // Twist.center ≤ a},
        evalCone q (fun i => (v i).1) a ≠ evalCone q (fun i => (v i).1) b := by
  classical
  simpa only [not_forall] using not_congr (equation_validity_transport q a b)

end Formula
end GaloisForLFunctions.HTGeometry.FrobeniusGalois
