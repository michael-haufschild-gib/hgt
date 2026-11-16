import GaloisForLFunctions.MetaplecticMobiusDescent.Descent.AngularMixedReflection
import GaloisForLFunctions.MetaplecticMobiusDescent.Reflection.AngularRowPhases
import GaloisForLFunctions.MetaplecticMobiusDescent.Reflection.AngularKernelTails

/-!
# Absolutely convergent angular reflected arrays

Mixed angular reflection reindexes into the same ramified, squarefree and cube ideals.
The column phase preserves the literal coefficient bound, so rapid angular kernel decay
supplies absolute summability without extra conductor powers.
-/

open Complex
open scoped BigOperators Classical ContDiff ComplexConjugate
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource CompletedGauss
open CompletedDyadic CanonicalRowCompletion SchwartzPlanePoisson NormalizedReflection
open CanonicalQuadraticSieve InverseMoment GaloisForLFunctions.FamilyContinuationTheory
namespace InverseReflectedPhase
noncomputable section
local notation "Eis" => Eisenstein.O
variable {ι : Type*} [Fintype ι] {N a c : Eis} {mode : Bool}

def angularLiteralRawCoefficient (ℓ : ℕ) (G : PrimeFamily ι)
    (D : ControlledStratumArithmetic G.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (j : ι→ℕ) (S : Finset ι) (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) : ℂ :=
  angularCuspColumnPhase ℓ u m n b * literalRawCoefficient G D s hc j S u m n b

lemma angularLiteralRawCoefficient_norm (ℓ : ℕ) (G : PrimeFamily ι)
    (D : ControlledStratumArithmetic G.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (hN : (9:Eis)*c∣N) (hbase : if mode then lambda^2∣a-1 else lambda^2∣c-1)
    (hchar : ∀ i, ringChar (Eis⧸G.ideal i)≠2) (j : ι→ℕ) (hj : ∀ i, j i<6)
    (S : Finset ι) (u : Eisˣ) (m : ℕ) (n b : NonzeroDualIdeal) :
    ‖angularLiteralRawCoefficient ℓ G D s hc j S u m n.val b.val‖≤(Ideal.absNorm (∏ i,G.ideal i):ℝ) := by
  rw [angularLiteralRawCoefficient,norm_mul]
  exact (mul_le_mul_of_nonneg_right (angularCuspColumnPhase_norm_le_one ℓ u m n.val b.val)
    (norm_nonneg _)).trans (by simpa only [one_mul] using
      literalRawCoefficient_norm G D s hc hN hbase hchar j hj S u m n b)

def angularLiteralRawSeries (ℓ : ℕ) (G : PrimeFamily ι)
    (D : ControlledStratumArithmetic G.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (j : ι→ℕ) (S : Finset ι) (W : ℝ→ℂ) (X : ℝ) (t : Eisˣ×RawTailIndex) : ℂ :=
  angularRawDualKernelTerm ℓ (Vstar W) (literalRawScale G s X) 1 completedRamifiedStep
    (angularLiteralRawCoefficient ℓ G D s hc j S t.1) t.2

lemma angularLiteralRawSeries_support (ℓ : ℕ) (G : PrimeFamily ι)
    (D : ControlledStratumArithmetic G.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (j : ι→ℕ) (S : Finset ι) (W : ℝ→ℂ) (X : ℝ) :
    Function.support (angularLiteralRawSeries ℓ G D s hc j S W X)⊆Set.range thetaRawIndex := by
  intro t ht
  have hp : Squarefree t.2.2.1.val ∧ primaryIdealGenerator t.2.2.1.val≠0 ∧ primaryIdealGenerator t.2.2.2.val≠0 := by
    by_contra hn
    exact ht (by simp only [angularLiteralRawSeries,angularRawDualKernelTerm,angularLiteralRawCoefficient,literalRawCoefficient,if_neg hn,mul_zero,zero_mul])
  exact ⟨(t.1,t.2.1,⟨t.2.2.1.val,hp.1,hp.2.1⟩,⟨t.2.2.2.val,hp.2.2⟩),rfl⟩

theorem angularMixedReflectedValue_eq_fullRaw (ℓ : ℕ) (G : PrimeFamily ι)
    (D : ControlledStratumArithmetic G.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (j : ι→ℕ) (S : Finset ι) (W : ℝ→ℂ) (X : ℝ) :
    angularMixedReflectedValue ℓ D s G.generator_ne_zero hc G.generator_good j S W X=
      fixedRadialCoefficientScalar*(s.stratumShapeFactor (c*∏ i,G.generator i)*elemPsiSix (c*∏ i,G.generator i)^(2*ℓ))*
        ∑' t : Eisˣ×RawTailIndex, angularLiteralRawSeries ℓ G D s hc j S W X t := by
  unfold angularMixedReflectedValue
  congr 1
  refine (tsum_congr ?_).trans (thetaRawIndex_injective.tsum_eq (angularLiteralRawSeries_support ℓ G D s hc j S W X))
  intro t
  have hx : sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency t)=
      s.modelDualNumerator t.1 t.2.1 t.2.2.1.val t.2.2.2.val := by
    rw [thetaFullFrequency_eq_fixedCuspArrayIndex]
    rfl
  unfold angularLiteralRawSeries angularRawDualKernelTerm angularLiteralRawCoefficient literalRawCoefficient thetaRawIndex literalRawScale
  rw [if_pos ⟨t.2.2.1.property.1,t.2.2.1.property.2,t.2.2.2.property⟩,hx]
  dsimp only
  rw [thetaFullFrequency_eq_fixedCuspArrayIndex]
  simp only [angularCuspColumnPhase,ramifiedScale, one_mul]
  ring

theorem angularLiteralRawSeries_summable_norm (ℓ : ℕ) (G : PrimeFamily ι)
    (D : ControlledStratumArithmetic G.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (hN : (9:Eis)*c∣N) (hbase : if mode then lambda^2∣a-1 else lambda^2∣c-1)
    (hchar : ∀ i, ringChar (Eis⧸G.ideal i)≠2) (j : ι→ℕ) (hj : ∀ i, j i<6)
    (S : Finset ι) (W : ℝ→ℂ) (lo hi : ℝ) (hlo : 0< lo)
    (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0< X) :
    Summable (fun t : Eisˣ×RawTailIndex => ‖angularLiteralRawSeries ℓ G D s hc j S W X t‖) := by
  let : Finite Eisˣ := cubic_units_finite
  let : Fintype Eisˣ := Fintype.ofFinite _
  apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
  refine ⟨?_,(hasSum_fintype _).summable⟩
  intro u
  exact angularRawDualKernelTerm_summable_norm ℓ (Vstar W) lo hi hlo (Vstar_support W lo hi hWs)
    (Vstar_contDiff W lo hi hlo hWs hW) (literalRawScale G s X) 1 completedRamifiedStep
    (Ideal.absNorm (∏ i,G.ideal i):ℝ) (literalRawScale_pos G s hc X hX) (by norm_num)
    completedRamifiedStep_gt_one (Nat.cast_nonneg _) (angularLiteralRawCoefficient ℓ G D s hc j S u)
    (angularLiteralRawCoefficient_norm ℓ G D s hc hN hbase hchar j hj S u)

end
end InverseReflectedPhase
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
