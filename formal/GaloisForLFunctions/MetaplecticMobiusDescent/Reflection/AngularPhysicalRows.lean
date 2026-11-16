import GaloisForLFunctions.MetaplecticMobiusDescent.Reflection.AngularKernelContraction
import GaloisForLFunctions.MetaplecticMobiusDescent.Inversion.ReflectedArithmeticHeight

/-!
# Angular kernels in reflected physical rows

The arithmetic coefficient decomposition is independent of the archimedean kernel.
Angular logarithmic separation therefore gives the same frozen-branch rows, under a common
integrable density with polynomial height bounds and the original terminal small-scale gain.
-/

open MeasureTheory Set
open scoped BigOperators Classical ContDiff ComplexConjugate SchwartzMap
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource CompletedGauss
open CanonicalRowCompletion SchwartzPlanePoisson NormalizedReflection JointLogSeparation
open CompletedDyadic CanonicalQuadraticSieve InverseMoment InverseKernelSourceUniform
namespace InverseReflectedPhase
noncomputable section
local notation "Eis" => Eisenstein.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

def angularKernelSourceTerm (ℓ : ℕ) (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (jF : φ→ℕ)
    (D : ControlledStratumArithmetic (F.reflected K hK S).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) (windows : Fin 4→ℝ→ℂ)
    (QK QP Qn Qb : ℝ) (W : ℝ→ℂ) (θ X : ℝ) : ℂ :=
  actualMixedCoefficient F K hK S jF D s hc u m n b *
    ((∏ i, windows i (kernelLogCoordinates QK QP Qn Qb (Ideal.absNorm K:ℝ)
      (Ideal.absNorm (∏ i, S.ideal i):ℝ) (Ideal.absNorm n:ℝ) (Ideal.absNorm b:ℝ) i)) /
      ((ramifiedScale 1 completedRamifiedStep m*Real.sqrt (Ideal.absNorm n:ℝ)*(Ideal.absNorm b:ℝ):ℝ):ℂ) *
      angularPaperKernel ℓ (Vstar (CompletedHeight.normTwistedSource W θ))
        ((X/(27*(sourceCuspScale s.index)^2*
          (Ideal.absNorm (Ideal.span {c*∏ i, (F.reflected K hK S).generator i}):ℝ)^2))*
          (ramifiedScale 1 completedRamifiedStep m)^3*(Ideal.absNorm n:ℝ)*(Ideal.absNorm b:ℝ)^3))

theorem angularKernelSourceTerm_numeric (ℓ : ℕ) (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (jF : φ→ℕ)
    (D : ControlledStratumArithmetic (F.reflected K hK S).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) (windows : Fin 4→ℝ→ℂ)
    (QK QP Qn Qb : ℝ) (W : ℝ→ℂ) (θ X : ℝ) :
    angularKernelSourceTerm ℓ F K hK S jF D s hc u m n b windows QK QP Qn Qb W θ X =
    actualMixedCoefficient F K hK S jF D s hc u m n b *
      ((∏ i, windows i (kernelLogCoordinates QK QP Qn Qb (Ideal.absNorm K:ℝ)
        (Ideal.absNorm (∏ i, S.ideal i):ℝ) (Ideal.absNorm n:ℝ) (Ideal.absNorm b:ℝ) i)) /
        ((ramifiedScale 1 completedRamifiedStep m*Real.sqrt (Ideal.absNorm n:ℝ)*(Ideal.absNorm b:ℝ):ℝ):ℂ) *
        angularPaperKernel ℓ (Vstar (CompletedHeight.normTwistedSource W θ))
          (actualKernelCoefficient F s m X*(Ideal.absNorm n:ℝ)*(Ideal.absNorm b:ℝ)^3/
            ((Ideal.absNorm K:ℝ)^2*(Ideal.absNorm (∏ i, S.ideal i):ℝ)^2))) := by
  unfold angularKernelSourceTerm
  rw [actual_theta_kernel_argument]

def angularWeightedFinitePhysicalKernelRow (ℓ : ℕ) (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : Ideal Eis→PrimeFamily σ) (jF : φ→ℕ) (Pset nset bset : Finset (Ideal Eis))
    (D : ∀ P : Pset, IsCoprime K P.val →
      ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (u : Eisˣ) (m : ℕ) (windows : Fin 4→ℝ→ℂ) (QK QP Qn Qb : ℝ)
    (W : ℝ→ℂ) (θ X : ℝ) (r₀ aw₀ : Ideal Eis→ℂ) (w₀ : Ideal Eis→Ideal Eis→ℂ) : ℂ :=
  ∑ x : CoprimeSourceIndex K Pset nset bset,
    (r₀ K*aw₀ x.1.val.val*w₀ x.2.1.val x.2.2.val)*angularKernelSourceTerm ℓ F K hK (S x.1.val.val) jF (D x.1.val x.1.property) s hc
      u m x.2.1.val x.2.2.val windows QK QP Qn Qb W θ X


end
end InverseReflectedPhase
namespace InverseReflectedArithmeticHeight
open InverseReflectedPhase
noncomputable section
local notation "Eis" => Eisenstein.O
universe u v w

theorem angular_actual_reflected_finite_source_arithmetic_uniform (ℓ : ℕ)
    (a₀ b₀ : ℝ) (ha₀ : 0<a₀) (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ)
    (hM : ∀ i, 0≤M i) (hwindows : ∀ i y, windows i y≠0 → |y|≤M i)
    (W : ℝ→ℂ) (hWsupport : Function.support W ⊆ Set.Icc a₀ b₀)
    (hW : ContDiff ℝ ∞ W) (J : ℕ) :
    ∃ (U : ℝ→ℂ) (degree : ℕ) (C₀ : ℝ), 0≤C₀ ∧ HasCompactSupport U ∧ ContDiff ℝ ∞ U ∧
      ∀ {N a c : Eis} {mode : Bool}, ∀ {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ], ∀ (F : PrimeFamily φ)
        (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
        (unit : Eisˣ) (m : ℕ) (θ X QK QP Qn Qb : ℝ),
        0<X → 0<QK → 0<QP → 0<Qn → 0<Qb →
      let R := kernelCenter (actualKernelCoefficient F s m X) QK QP Qn Qb
      (∀ {κ : Type w} (source : Finset κ) (weight : κ→ℂ)
        (K : κ→Ideal Eis) (hK : ∀ j, Admissible (K j)) (S : κ→PrimeFamily σ) (jF : φ→ℕ)
        (D : ∀ j, ControlledStratumArithmetic (F.reflected (K j) (hK j) (S j)).generator N a c mode)
        (n b : κ→Ideal Eis), (∀ j ∈ source, n j≠0 ∧ b j≠0) →
        (∑ j ∈ source, weight j*angularKernelSourceTerm ℓ F (K j) (hK j) (S j) jF (D j) s hc
          unit m (n j) (b j) windows QK QP Qn Qb W θ X) =
        ((Real.exp (M 2/2+M 3)/(ramifiedScale 1 completedRamifiedStep m*Real.sqrt Qn*Qb)*smallScalar R:ℝ):ℂ)*
          ∫ t : ℝ, angularTwistedDensity ℓ U W θ R t *
            ∑ j ∈ source, (weight j*actualMixedCoefficient F (K j) (hK j) (S j) jF (D j) s hc unit m (n j) (b j))*
              (kernelCoordinateWeight (reciprocalKernelWindows windows M 0) (-2) QK t (Ideal.absNorm (K j):ℝ)*
                kernelCoordinateWeight (reciprocalKernelWindows windows M 1) (-2) QP t (Ideal.absNorm (∏ i, (S j).ideal i):ℝ)*
                kernelDualWeight (reciprocalKernelWindows windows M) Qn Qb t (Ideal.absNorm (n j):ℝ) (Ideal.absNorm (b j):ℝ))) ∧
      Integrable (angularTwistedDensity ℓ U W θ R) ∧
      Integrable (fun t : ℝ => (1+‖t‖)^J*‖angularTwistedDensity ℓ U W θ R t‖) ∧
      (∫ t : ℝ, (1+‖t‖)^J*‖angularTwistedDensity ℓ U W θ R t‖) ≤ C₀*(1+‖θ‖)^degree ∧
      (∀ t : ℝ, (1+‖t‖)^J*‖angularTwistedDensity ℓ U W θ R t‖ ≤ C₀*(1+‖θ‖)^degree) := by
  obtain ⟨U,degree,C₀,hC₀,hUc,hUs,hsep⟩ := angular_reflected_finite_source_uniform.{w} ℓ
    a₀ b₀ ha₀ windows M hM hwindows W hWsupport hW J
  refine ⟨U,degree,C₀,hC₀,hUc,hUs,?_⟩
  intro N a c mode φ σ _ _ F s hc unit m θ X QK QP Qn Qb hX hQK hQP hQn hQb
  have hr := ramifiedScale_pos 1 completedRamifiedStep (by norm_num)
    (lt_trans zero_lt_one completedRamifiedStep_gt_one) m
  obtain ⟨he,hi,hiJ,hm,hp⟩ := hsep θ (actualKernelCoefficient F s m X) QK QP Qn Qb
    (ramifiedScale 1 completedRamifiedStep m) (actualKernelCoefficient_pos F s hc m X hX)
    hQK hQP hQn hQb hr
  refine ⟨?_,hi,hiJ,hm,hp⟩
  intro κ source weight K hK S jF D n b hn
  have hnorm (I : Ideal Eis) (hI : I≠0) : (0:ℝ)<Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hpos (j : κ) (hj : j ∈ source) : (0:ℝ)<Ideal.absNorm (K j) ∧
      (0:ℝ)<Ideal.absNorm (∏ i, (S j).ideal i) ∧ (0:ℝ)<Ideal.absNorm (n j) ∧ (0:ℝ)<Ideal.absNorm (b j) :=
    ⟨hnorm _ (hK j).1,hnorm _ (Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne ((S j).ideal i))),
      hnorm _ (hn j hj).1,hnorm _ (hn j hj).2⟩
  have hh := he source (fun j => weight j*actualMixedCoefficient F (K j) (hK j) (S j) jF (D j) s hc unit m (n j) (b j))
    (fun j => (Ideal.absNorm (K j):ℝ)) (fun j => (Ideal.absNorm (∏ i, (S j).ideal i):ℝ))
    (fun j => (Ideal.absNorm (n j):ℝ)) (fun j => (Ideal.absNorm (b j):ℝ)) hpos
  simpa only [angularKernelSourceTerm_numeric,mul_assoc] using hh

theorem angular_weighted_finite_physical_row_common_measure_arithmetic_uniform (ℓ : ℕ)
    (a₀ b₀ : ℝ) (ha₀ : 0<a₀) (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ)
    (hM : ∀ i, 0≤M i) (hwindows : ∀ i y, windows i y≠0 → |y|≤M i)
    (W : ℝ→ℂ) (hWsupport : Function.support W ⊆ Set.Icc a₀ b₀)
    (hW : ContDiff ℝ ∞ W) (J : ℕ) :
    ∃ (U : ℝ→ℂ) (degree : ℕ) (C₀ : ℝ), 0≤C₀ ∧ HasCompactSupport U ∧ ContDiff ℝ ∞ U ∧
      ∀ {N a c : Eis} {mode : Bool}, ∀ {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ], ∀ (F : PrimeFamily φ)
        (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
        (unit : Eisˣ) (m : ℕ) (θ X QK QP Qn Qb : ℝ),
        0<X → 0<QK → 0<QP → 0<Qn → 0<Qb →
      let R := kernelCenter (actualKernelCoefficient F s m X) QK QP Qn Qb
      (∀ (K : Ideal Eis) (hK : Admissible K) (S : Ideal Eis→PrimeFamily σ) (jF : φ→ℕ)
        (Pset nset bset : Finset (Ideal Eis))
        (D : ∀ P : Pset, IsCoprime K P.val →
          ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode),
        (∀ P ∈ Pset, (∏ i, (S P).ideal i)=P) → (∀ n ∈ nset, n≠0) → (∀ b ∈ bset, b≠0) →
        ∀ (r₀ aw₀ : Ideal Eis→ℂ) (w₀ : Ideal Eis→Ideal Eis→ℂ),
        angularWeightedFinitePhysicalKernelRow ℓ F K hK S jF Pset nset bset D s hc unit m windows QK QP Qn Qb W θ X r₀ aw₀ w₀ =
        ((Real.exp (M 2/2+M 3)/(ramifiedScale 1 completedRamifiedStep m*Real.sqrt Qn*Qb)*smallScalar R:ℝ):ℂ)*
          ∫ t : ℝ, angularTwistedDensity ℓ U W θ R t *
            weightedPhysicalReflectedRow F K hK S jF Pset nset bset D s hc
              (fun K => r₀ K*kernelCoordinateWeight (reciprocalKernelWindows windows M 0) (-2) QK t (Ideal.absNorm K:ℝ))
              (fun P => aw₀ P*kernelCoordinateWeight (reciprocalKernelWindows windows M 1) (-2) QP t (Ideal.absNorm P:ℝ))
              (fun n b => w₀ n b*kernelDualWeight (reciprocalKernelWindows windows M) Qn Qb t (Ideal.absNorm n:ℝ) (Ideal.absNorm b:ℝ)) unit m) ∧
      Integrable (angularTwistedDensity ℓ U W θ R) ∧
      Integrable (fun t : ℝ => (1+‖t‖)^J*‖angularTwistedDensity ℓ U W θ R t‖) ∧
      (∫ t : ℝ, (1+‖t‖)^J*‖angularTwistedDensity ℓ U W θ R t‖) ≤ C₀*(1+‖θ‖)^degree ∧
      (∀ t : ℝ, (1+‖t‖)^J*‖angularTwistedDensity ℓ U W θ R t‖ ≤ C₀*(1+‖θ‖)^degree) := by
  obtain ⟨U,degree,C₀,hC₀,hUc,hUs,hsep⟩ := angular_actual_reflected_finite_source_arithmetic_uniform ℓ
    a₀ b₀ ha₀ windows M hM hwindows W hWsupport hW J
  refine ⟨U,degree,C₀,hC₀,hUc,hUs,?_⟩
  intro N a c mode φ σ _ _ F s hc unit m θ X QK QP Qn Qb hX hQK hQP hQn hQb
  obtain ⟨he,hi,hiJ,hm,hp⟩ := hsep (N:=N) (a:=a) (c:=c) (mode:=mode) (φ:=φ) (σ:=σ) F s hc unit m θ X QK QP Qn Qb hX hQK hQP hQn hQb
  refine ⟨?_,hi,hiJ,hm,hp⟩
  intro K hK S jF Pset nset bset D hprod hn hb r₀ aw₀ w₀
  let T := CoprimeSourceIndex K Pset nset bset
  have hh := he (Finset.univ : Finset T) (fun x => r₀ K*aw₀ x.1.val.val*w₀ x.2.1.val x.2.2.val) (fun _ => K) (fun _ => hK)
    (fun x => S x.1.val.val) jF (fun x => D x.1.val x.1.property)
    (fun x => x.2.1.val) (fun x => x.2.2.val)
    (fun x _ => ⟨hn _ x.2.1.property,hb _ x.2.2.property⟩)
  unfold angularWeightedFinitePhysicalKernelRow
  rw [hh]
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  dsimp only [T]
  congr 1
  rw [weightedPhysicalReflectedRow_eq_coprime_source]
  apply Finset.sum_congr rfl
  intro x hx
  rw [hprod x.1.val.val x.1.val.property]
  ring

theorem angular_weighted_finite_physical_row_branch_measure_arithmetic_uniform (ℓ : ℕ)
    (a₀ b₀ : ℝ) (ha₀ : 0<a₀) (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ)
    (hM : ∀ i, 0≤M i) (hwindows : ∀ i y, windows i y≠0 → |y|≤M i)
    (W : ℝ→ℂ) (hWsupport : Function.support W ⊆ Set.Icc a₀ b₀)
    (hW : ContDiff ℝ ∞ W) (J : ℕ) :
    ∃ (U : ℝ→ℂ) (degree : ℕ) (C₀ : ℝ), 0≤C₀ ∧ HasCompactSupport U ∧ ContDiff ℝ ∞ U ∧
      ∀ {N a c : Eis} {mode : Bool}, ∀ {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ], ∀ (F : PrimeFamily φ)
        (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
        (unit : Eisˣ) (m : ℕ) (θ X QK QP Qn Qb : ℝ),
        0<X → 0<QK → 0<QP → 0<Qn → 0<Qb →
      let R := kernelCenter (actualKernelCoefficient F s m X) QK QP Qn Qb
      (∀ (K : Ideal Eis) (hK : Admissible K) (S : Ideal Eis→PrimeFamily σ) (jF : φ→ℕ)
        (Pset nset bset : Finset (Ideal Eis))
        (D : ∀ P : Pset, IsCoprime K P.val →
          ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode),
        (∀ P ∈ Pset, (∏ i, (S P).ideal i)=P) → (∀ n ∈ nset, n≠0) → (∀ b ∈ bset, b≠0) →
        ∀ (r₀ aw₀ : Ideal Eis→ℂ) (w₀ : Ideal Eis→Ideal Eis→ℂ),
        ∀ {ι : Type*} [Fintype ι] (G0 : PrimeFamily ι)
          (D0 : ControlledStratumArithmetic G0.generator N a c mode),
        (∀ P : Pset, IsCoprime K P.val → Pairwise (Function.onFun IsCoprime (F.reflected K hK (S P.val)).ideal)) →
        (∀ P hp, (D P hp).fixedFactor=D0.fixedFactor) →
        (∀ P hp u m n b, actualCuspColumn (D P hp) s hc u m n b=actualCuspColumn D0 s hc u m n b) →
        (∀ b ∈ bset, primaryIdealGenerator b≠0) →
        angularWeightedFinitePhysicalKernelRow ℓ F K hK S jF Pset nset bset D s hc unit m windows QK QP Qn Qb W θ X r₀ aw₀ w₀ =
        ((Real.exp (M 2/2+M 3)/(ramifiedScale 1 completedRamifiedStep m*Real.sqrt Qn*Qb)*smallScalar R:ℝ):ℂ)*
          ∫ t : ℝ, angularTwistedDensity ℓ U W θ R t *
            (∑ e : φ→Fin 3, weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
              (actualCuspColumn D0 s hc unit m)
              (fun K => r₀ K*kernelCoordinateWeight (reciprocalKernelWindows windows M 0) (-2) QK t (Ideal.absNorm K:ℝ))
              (fun P => aw₀ P*kernelCoordinateWeight (reciprocalKernelWindows windows M 1) (-2) QP t (Ideal.absNorm P:ℝ))
              (fun n b => w₀ n b*kernelDualWeight (reciprocalKernelWindows windows M) Qn Qb t (Ideal.absNorm n:ℝ) (Ideal.absNorm b:ℝ)) unit m Pset nset bset K)) ∧
      Integrable (angularTwistedDensity ℓ U W θ R) ∧
      Integrable (fun t : ℝ => (1+‖t‖)^J*‖angularTwistedDensity ℓ U W θ R t‖) ∧
      (∫ t : ℝ, (1+‖t‖)^J*‖angularTwistedDensity ℓ U W θ R t‖) ≤ C₀*(1+‖θ‖)^degree ∧
      (∀ t : ℝ, (1+‖t‖)^J*‖angularTwistedDensity ℓ U W θ R t‖ ≤ C₀*(1+‖θ‖)^degree) := by
  obtain ⟨U,degree,C₀,hC₀,hUc,hUs,hsep⟩ := angular_weighted_finite_physical_row_common_measure_arithmetic_uniform ℓ
    a₀ b₀ ha₀ windows M hM hwindows W hWsupport hW J
  refine ⟨U,degree,C₀,hC₀,hUc,hUs,?_⟩
  intro N a c mode φ σ _ _ F s hc unit m θ X QK QP Qn Qb hX hQK hQP hQn hQb
  obtain ⟨he,hi,hiJ,hm,hp⟩ := hsep (N:=N) (a:=a) (c:=c) (mode:=mode) (φ:=φ) (σ:=σ) F s hc unit m θ X QK QP Qn Qb hX hQK hQP hQn hQb
  refine ⟨?_,hi,hiJ,hm,hp⟩
  intro K hK S jF Pset nset bset D hprod hn hb r₀ aw₀ w₀ ι _ G0 D0 hcop hκ hA hbgen
  rw [he K hK S jF Pset nset bset D hprod hn hb r₀ aw₀ w₀]
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  congr 1
  exact weightedPhysicalReflectedRow_eq_branches F K hK S jF Pset nset bset hprod D hcop
    G0 D0 s hc hκ hA hbgen _ _ _ unit m

end
end InverseReflectedArithmeticHeight
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
