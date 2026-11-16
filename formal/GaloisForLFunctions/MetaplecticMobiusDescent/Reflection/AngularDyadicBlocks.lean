import GaloisForLFunctions.MetaplecticMobiusDescent.Reflection.AngularLiteralArrays
import GaloisForLFunctions.MetaplecticMobiusDescent.Reflection.AngularPhysicalRows

/-!
# Angular reflected dyadic blocks

Absolute angular reflection splits into the same dyadic ideal shells. The frequency
character is a bounded column weight in each finite physical row.
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

def angularLiteralDyadicBlock (ℓ : ℕ) (G : PrimeFamily ι)
    (D : ControlledStratumArithmetic G.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (j : ι→ℕ) (S : Finset ι) (W : ℝ→ℂ) (X : ℝ) (u : Eisˣ) (i : ℕ×ℕ×ℕ) : ℂ :=
  ∑ n : dualIdealDyad i.2.2, ∑ b : dualIdealDyad i.2.1,
    angularLiteralRawSeries ℓ G D s hc j S W X
      (u,i.1,⟨n.val,((mem_dualIdealDyad _ _).mp n.property).1⟩,
        ⟨b.val,((mem_dualIdealDyad _ _).mp b.property).1⟩)

theorem angularMixedReflectedValue_eq_dyadic (ℓ : ℕ) (G : PrimeFamily ι)
    (D : ControlledStratumArithmetic G.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (hN : (9:Eis)*c∣N) (hbase : if mode then lambda^2∣a-1 else lambda^2∣c-1)
    (hchar : ∀ i, ringChar (Eis⧸G.ideal i)≠2) (j : ι→ℕ) (hj : ∀ i, j i<6)
    (S : Finset ι) (W : ℝ→ℂ) (lo hi : ℝ) (hlo : 0< lo)
    (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0< X) :
    angularMixedReflectedValue ℓ D s G.generator_ne_zero hc G.generator_good j S W X=
      fixedRadialCoefficientScalar*(s.stratumShapeFactor (c*∏ i,G.generator i)*elemPsiSix (c*∏ i,G.generator i)^(2*ℓ))*
        ∑' u : Eisˣ, ∑' i : ℕ×ℕ×ℕ, angularLiteralDyadicBlock ℓ G D s hc j S W X u i := by
  have hs := (angularLiteralRawSeries_summable_norm ℓ G D s hc hN hbase hchar j hj S W lo hi hlo hWs hW X hX).of_norm
  rw [angularMixedReflectedValue_eq_fullRaw,hs.tsum_prod]
  congr 1
  apply tsum_congr
  intro u
  exact tsum_dualIdealDyads _ (hs.prod_factor u)


lemma angularLiteralDyadicBlock_summable (ℓ : ℕ) (G : PrimeFamily ι)
    (D : ControlledStratumArithmetic G.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (hN : (9:Eis)*c∣N) (hbase : if mode then lambda^2∣a-1 else lambda^2∣c-1)
    (hchar : ∀ i, ringChar (Eis⧸G.ideal i)≠2) (j : ι→ℕ) (hj : ∀ i, j i<6)
    (S : Finset ι) (W : ℝ→ℂ) (lo hi : ℝ) (hlo : 0< lo)
    (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0< X) (u : Eisˣ) :
    Summable (angularLiteralDyadicBlock ℓ G D s hc j S W X u) := by
  have hs := ((angularLiteralRawSeries_summable_norm ℓ G D s hc hN hbase hchar j hj S W lo hi hlo hWs hW X hX).of_norm).prod_factor u
  have hh := (dualDyadicIndexEquiv.symm.summable_iff.mpr hs).sigma
  apply hh.congr
  intro i
  simp only [tsum_fintype,Fintype.sum_prod_type,angularLiteralDyadicBlock,Function.comp_apply]
  rfl


variable {φ σ : Type*} [Fintype φ] [Fintype σ]

theorem angularLiteralRawSeries_eq_shell_source (ℓ : ℕ) (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (jF : φ→ℕ)
    (D : ControlledStratumArithmetic (F.reflected K hK S).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (u : Eisˣ) (i : ℕ×ℕ×ℕ) (n : dualIdealDyad i.2.2) (b : dualIdealDyad i.2.1)
    (QK QP : ℝ) (hQK : 0< QK) (hQP : 0< QP)
    (hKr : QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤ QK)
    (hPr : QP/2≤(Ideal.absNorm (∏ i,S.ideal i):ℝ) ∧ (Ideal.absNorm (∏ i,S.ideal i):ℝ)≤ QP)
    (W : ℝ→ℂ) (θ X : ℝ) :
    angularLiteralRawSeries ℓ (F.reflected K hK S) D s hc (reflectedExponent jF)
      (slotIndices φ (PrimeIndex K) σ) (CompletedHeight.normTwistedSource W θ) X
      (u,i.1,⟨n.val,((mem_dualIdealDyad _ _).mp n.property).1⟩,
        ⟨b.val,((mem_dualIdealDyad _ _).mp b.property).1⟩)=
    if CubicSieve.Admissible n.val ∧ primaryIdealGenerator b.val≠0 then
      (angularCuspColumnPhase ℓ u i.1 n.val b.val)*angularKernelSourceTerm ℓ F K hK S jF D s hc u i.1 n.val b.val
        (fun _ => completedShellWindow) QK QP ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1) W θ X else 0 := by
  have hw := shell_windows_one QK QP hQK hQP K (∏ i,S.ideal i) hK.1
    (Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (S.ideal i))) hKr hPr i.2.1 i.2.2 n b
  by_cases hp : CubicSieve.Admissible n.val ∧ primaryIdealGenerator b.val≠0
  · have hp' : Squarefree n.val ∧ primaryIdealGenerator n.val≠0 ∧ primaryIdealGenerator b.val≠0 :=
      ⟨hp.1.1,hp.1.2,hp.2⟩
    rw [if_pos hp]
    unfold angularLiteralRawSeries angularRawDualKernelTerm angularLiteralRawCoefficient literalRawCoefficient angularKernelSourceTerm actualMixedCoefficient literalRawScale
    rw [if_pos hp',hw]
    dsimp only
    simp only [ramifiedScale,one_mul]
    ring
  · have hp' : ¬(Squarefree n.val ∧ primaryIdealGenerator n.val≠0 ∧ primaryIdealGenerator b.val≠0) :=
      fun h => hp ⟨⟨h.1,h.2.1⟩,h.2.2⟩
    simp only [if_neg hp,angularLiteralRawSeries,angularRawDualKernelTerm,angularLiteralRawCoefficient,literalRawCoefficient,if_neg hp',mul_zero,zero_mul]

theorem angularLiteralDyadicBlock_eq_shell_source (ℓ : ℕ) (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (jF : φ→ℕ)
    (D : ControlledStratumArithmetic (F.reflected K hK S).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (u : Eisˣ) (i : ℕ×ℕ×ℕ) (QK QP : ℝ) (hQK : 0< QK) (hQP : 0< QP)
    (hKr : QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤ QK)
    (hPr : QP/2≤(Ideal.absNorm (∏ i,S.ideal i):ℝ) ∧ (Ideal.absNorm (∏ i,S.ideal i):ℝ)≤ QP)
    (W : ℝ→ℂ) (θ X : ℝ) :
    angularLiteralDyadicBlock ℓ (F.reflected K hK S) D s hc (reflectedExponent jF)
      (slotIndices φ (PrimeIndex K) σ) (CompletedHeight.normTwistedSource W θ) X u i=
      ∑ n : dualIdealDyad i.2.2, ∑ b : dualIdealDyad i.2.1,
        if CubicSieve.Admissible n.val ∧ primaryIdealGenerator b.val≠0 then
          (angularCuspColumnPhase ℓ u i.1 n.val b.val)*angularKernelSourceTerm ℓ F K hK S jF D s hc u i.1 n.val b.val
            (fun _ => completedShellWindow) QK QP ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1) W θ X else 0 := by
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro b hb
  exact angularLiteralRawSeries_eq_shell_source ℓ F K hK S jF D s hc u i n b QK QP hQK hQP hKr hPr W θ X

theorem angularLiteralDyadicBlock_eq_filtered_source (ℓ : ℕ) (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (jF : φ→ℕ)
    (D : ControlledStratumArithmetic (F.reflected K hK S).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (u : Eisˣ) (i : ℕ×ℕ×ℕ) (QK QP : ℝ) (hQK : 0< QK) (hQP : 0< QP)
    (hKr : QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤ QK)
    (hPr : QP/2≤(Ideal.absNorm (∏ i,S.ideal i):ℝ) ∧ (Ideal.absNorm (∏ i,S.ideal i):ℝ)≤ QP)
    (W : ℝ→ℂ) (θ X : ℝ) :
    angularLiteralDyadicBlock ℓ (F.reflected K hK S) D s hc (reflectedExponent jF)
      (slotIndices φ (PrimeIndex K) σ) (CompletedHeight.normTwistedSource W θ) X u i=
      ∑ n : reflectedNDyad i.2.2, ∑ b : reflectedBDyad i.2.1,
        angularCuspColumnPhase ℓ u i.1 n.val b.val*angularKernelSourceTerm ℓ F K hK S jF D s hc u i.1 n.val b.val
          (fun _ => completedShellWindow) QK QP ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1) W θ X := by
  rw [angularLiteralDyadicBlock_eq_shell_source ℓ F K hK S jF D s hc u i QK QP hQK hQP hKr hPr W θ X]
  exact sum_dual_mask i.2.1 i.2.2 (fun n b => angularCuspColumnPhase ℓ u i.1 n b*angularKernelSourceTerm ℓ F K hK S jF D s hc u i.1 n b
    (fun _ => completedShellWindow) QK QP ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1) W θ X)

end
end InverseReflectedPhase
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
