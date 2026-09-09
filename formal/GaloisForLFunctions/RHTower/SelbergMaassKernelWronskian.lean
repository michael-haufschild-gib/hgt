import GaloisForLFunctions.RHTower.SelbergMaassPhaseStress
import GaloisForLFunctions.RHTower.SelbergMaassSliceRigidity

/-!
# Original arithmetic cross-frequency currents and positive cusp-tail kernel

The full complex inversion-transfer loss is expressed through its actual arithmetic
convolution kernel, retaining character phases and composite-level annihilator fibres.
Original coefficient ODEs give an exact mixed Wronskian transport law: the common
Maass potential cancels. Genuine cusp integrability proves current decay at infinity,
identifies its boundary value with the full tail Gram kernel, and proves positivity
for every finite complex superposition. The resulting Cauchy bound controls each
original mixed boundary current by its two tail-loss masses. Distinct residue channels
cancel exactly; opposite indices have zero Wronskian. No spectral estimate or boundary
sign is assumed, and the full quotient-core quarter comparison remains unproved.
-/

open Complex Set UpperHalfPlane ModularGroup MeasureTheory
open scoped BigOperators
namespace GaloisForLFunctions.RHTower.SelbergMaassKernelWronskian
open SelbergMaassCongruenceTrace SelbergMaassCongruenceAverage SelbergMaassUnipotentBlocks
open SelbergMaassCharacterProjection SelbergMaassCharacterFourier SelbergMaassInversionGram
open SelbergMaassUnipotentFourier SelbergMaassCharacterGradient SelbergMaassFourier
open SelbergMaassPhaseStress SelbergMaassMixedLoss SelbergMaassSliceRigidity
open GaloisForLFunctions.HTGeometry
noncomputable section
local instance gammaNormal (N : ℕ) : (CongruenceSubgroup.Gamma (N+1)).Normal :=
  CongruenceSubgroup.Gamma_normal (N+1)
variable (N : ℕ) (r s : ZMod (N+1))

/-- The actual Gram operator recovers the full complex mixed transfer pairing. -/
theorem transferGram_mixed (v w : EuclideanSpace ℂ (Deck N)) :
    inner ℂ (transferGram N r s v) w=
      inner ℂ (inversionTransfer N r s v) (inversionTransfer N r s w) := by
  unfold transferGram
  simp only [LinearMap.comp_apply]
  rw [characterProjection_self_adjoint,characterProjection_lower_conjugate,neg_neg,
    LinearIsometryEquiv.inner_map_eq_flip,regularUnitary_symm]
  simp only [← QuotientGroup.mk_inv]
  rw [characterProjection_inner_left]
  rfl

/-- The full complex original loss form, retaining phases and both slots. -/
def complexLoss (v w : EuclideanSpace ℂ (Deck N)) : ℂ :=
  inner ℂ v w-inner ℂ (inversionTransfer N r s v) (inversionTransfer N r s w)

/-- Its real part is precisely the physical mixed loss. -/
theorem complexLoss_re (v w : EuclideanSpace ℂ (Deck N)) :
    (complexLoss N r s v w).re=lossPair N r s v w := rfl

/-- The original loss form equals the full complement-Gram pairing. -/
theorem complexLoss_eq_gram (v w : EuclideanSpace ℂ (Deck N)) :
    complexLoss N r s v w=inner ℂ (v-transferGram N r s v) w := by
  rw [inner_sub_left,transferGram_mixed]
  rfl

/-- The actual Gram-loss form is Hermitian. -/
theorem complexLoss_conj (v w : EuclideanSpace ℂ (Deck N)) :
    (starRingEnd ℂ) (complexLoss N r s v w)=complexLoss N r s w v := by
  simp only [complexLoss,map_sub,inner_conj_symm]

/-- The actual mixed pairing has the kernel in its second slot. -/
theorem complexLoss_eq_gram_right (v w : EuclideanSpace ℂ (Deck N)) :
    complexLoss N r s v w=inner ℂ v (w-transferGram N r s w) := by
  rw [← complexLoss_conj N r s w v,complexLoss_eq_gram,inner_conj_symm]

/-- Every original arithmetic phase and nonunit collision fibre survives in the exact mixed kernel. -/
theorem complexLoss_convolution (v w : EuclideanSpace ℂ (Deck N)) :
    complexLoss N r s v w=inner ℂ v w-
      ∑ q : Deck N, ∑ g : Deck N,
        (starRingEnd ℂ) (v q)*gramKernel N r s g*w (q*g) := by
  rw [complexLoss_eq_gram_right,inner_sub_right,PiLp.inner_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  rw [RCLike.inner_apply,transferGram_convolution,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro g _
  ring

private theorem complexLoss_smul_left (a : ℂ) (v w : EuclideanSpace ℂ (Deck N)) :
    complexLoss N r s (a • v) w=(starRingEnd ℂ) a*complexLoss N r s v w := by
  simp only [complexLoss,map_smul,inner_smul_left,mul_sub]

private theorem complexLoss_smul_right (a : ℂ) (v w : EuclideanSpace ℂ (Deck N)) :
    complexLoss N r s v (a • w)=a*complexLoss N r s v w := by
  simp only [complexLoss,map_smul,inner_smul_right,mul_sub]

/-- The full original complex loss on the diagonal is its nonnegative physical energy. -/
theorem complexLoss_self (v : EuclideanSpace ℂ (Deck N)) :
    complexLoss N r s v v=(lossEnergy N r s v : ℂ) := by
  simp only [complexLoss,inner_self_eq_norm_sq_to_K,lossEnergy,Complex.ofReal_sub,Complex.ofReal_pow]
  rfl

private theorem complexLoss_norm_le (v w : EuclideanSpace ℂ (Deck N)) :
    ‖complexLoss N r s v w‖ ≤ ‖v‖^2+‖w‖^2 := by
  have ht (a : EuclideanSpace ℂ (Deck N)) : ‖inversionTransfer N r s a‖ ≤ ‖a‖ := by
    have h := lossEnergy_nonneg N r s a
    unfold lossEnergy at h
    nlinarith [norm_nonneg a,norm_nonneg (inversionTransfer N r s a)]
  calc
    _ ≤ ‖inner ℂ v w‖+‖inner ℂ (inversionTransfer N r s v) (inversionTransfer N r s w)‖ := norm_sub_le _ _
    _ ≤ ‖v‖*‖w‖+‖inversionTransfer N r s v‖*‖inversionTransfer N r s w‖ :=
      add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ ≤ ‖v‖*‖w‖+‖v‖*‖w‖ :=
      add_le_add_right (mul_le_mul (ht v) (ht w) (norm_nonneg _) (norm_nonneg _)) _
    _ ≤ _ := by nlinarith [sq_nonneg (‖v‖-‖w‖)]

/-- Complete finite source superpositions retain every complex Gram cross term. -/
theorem complexLoss_sum {ι : Type*} (I : Finset ι) (a : ι → ℂ)
    (v : ι → EuclideanSpace ℂ (Deck N)) :
    complexLoss N r s (∑ i ∈ I, a i • v i) (∑ j ∈ I, a j • v j)=
      ∑ i ∈ I, ∑ j ∈ I, (starRingEnd ℂ) (a i)*a j*complexLoss N r s (v i) (v j) := by
  conv_rhs => rw [Finset.sum_comm]
  simp only [complexLoss,map_sum,map_smul,sum_inner,inner_sum,inner_smul_left,
    inner_smul_right,Finset.mul_sum,mul_sub]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem complexLoss_hasDerivAt {u v : ℝ → EuclideanSpace ℂ (Deck N)}
    {u' v' : EuclideanSpace ℂ (Deck N)} {y : ℝ}
    (hu : HasDerivAt u u' y) (hv : HasDerivAt v v' y) :
    HasDerivAt (fun t => complexLoss N r s (u t) (v t))
      (complexLoss N r s (u y) v'+complexLoss N r s u' (v y)) y := by
  let T := (inversionTransfer N r s).toContinuousLinearMap.restrictScalars ℝ
  have h := (hu.inner ℂ hv).sub
    ((T.hasFDerivAt.comp_hasDerivAt y hu).inner ℂ (T.hasFDerivAt.comp_hasDerivAt y hv))
  convert h using 1 <;> try rfl
  simp only [complexLoss]
  dsimp [T]
  ring

variable {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N+1))) lam)

/-- The full original height vector satisfies its actual modal second-order equation. -/
theorem coefficientHeightVector_hasDerivAt (n : ℤ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (coefficientHeightVector N f n)
      (((signedFrequency (N+1 : ℕ) n^2-lam/y^2 : ℝ) : ℂ) • coefficientVector N f n y) y := by
  have hq (q : Deck N) := maassCoefficient_second_hasDerivAt N (quotientForm N f q) n hy
  simp_rw [maassCoefficient_second_eq N (quotientForm N f _) n hy] at hq
  have h := hasDerivAt_pi.mpr hq
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Deck N => ℂ)).symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt y h

/-- The actual arithmetic mixed coefficient kernel at physical height. -/
def coefficientLoss (n m : ℤ) (y : ℝ) : ℂ :=
  complexLoss N r s (coefficientVector N f n y) (coefficientVector N f m y)

/-- Original cross-frequency loss current, with both differentiated slots retained. -/
def coefficientWronskian (n m : ℤ) (y : ℝ) : ℂ :=
  complexLoss N r s (coefficientHeightVector N f n y) (coefficientVector N f m y)-
    complexLoss N r s (coefficientVector N f n y) (coefficientHeightVector N f m y)

/-- The common Maass potential cancels exactly in the full arithmetic mixed current. -/
theorem coefficientWronskian_hasDerivAt (n m : ℤ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (coefficientWronskian N r s f n m)
      (((signedFrequency (N+1 : ℕ) n^2-signedFrequency (N+1 : ℕ) m^2 : ℝ) : ℂ)*
        coefficientLoss N r s f n m y) y := by
  have hn := coefficientVector_hasDerivAt N f n hy
  have hm := coefficientVector_hasDerivAt N f m hy
  have hn' := coefficientHeightVector_hasDerivAt N f n hy
  have hm' := coefficientHeightVector_hasDerivAt N f m hy
  have h := (complexLoss_hasDerivAt N r s hn' hm).sub
    (complexLoss_hasDerivAt N r s hn hm')
  convert h using 1 <;> try rfl
  simp only [complexLoss_smul_left,complexLoss_smul_right,
    coefficientLoss,Complex.ofReal_sub,map_sub,Complex.conj_ofReal]
  ring

/-- The actual coefficient loss is continuous throughout the positive height ray. -/
theorem coefficientLoss_continuousOn (n m : ℤ) :
    ContinuousOn (coefficientLoss N r s f n m) (Ioi 0) := by
  intro y hy
  exact (complexLoss_hasDerivAt N r s
    (coefficientVector_hasDerivAt N f n hy)
    (coefficientVector_hasDerivAt N f m hy)).continuousAt.continuousWithinAt

/-- Exact transport of original off-diagonal arithmetic currents between any two positive cutoffs. -/
theorem coefficientWronskian_transport (n m : ℤ) {Y Z : ℝ} (hY : 0 < Y) (hZ : 0 < Z) :
    coefficientWronskian N r s f n m Z-coefficientWronskian N r s f n m Y=
      ((signedFrequency (N+1 : ℕ) n^2-signedFrequency (N+1 : ℕ) m^2 : ℝ) : ℂ)*
        ∫ y in Y..Z, coefficientLoss N r s f n m y := by
  have hp {y : ℝ} (hy : y ∈ uIcc Y Z) : 0 < y := (lt_min hY hZ).trans_le hy.1
  have hc := (coefficientLoss_continuousOn N r s f n m).mono (fun _ hy => hp hy)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y hy => coefficientWronskian_hasDerivAt N r s f n m (hp hy))
    ((hc.const_mul _).intervalIntegrable)
  rw [intervalIntegral.integral_const_mul] at h
  exact h.symm

/-- Distinct original frequency residues have exactly zero full complex arithmetic loss. -/
theorem coefficientLoss_eq_zero_of_residue_ne (n m : ℤ)
    (hnm : (n : ZMod (N+1))≠(m : ZMod (N+1))) {y : ℝ} (hy : 0 < y) :
    coefficientLoss N r s f n m y=0 := by
  have hfix (k : ℤ) : characterProjection N (upperBlock N) (k : ZMod (N+1))
      (coefficientVector N f k y)=coefficientVector N f k y := by
    rw [upperProjection_coefficientVector N f (k : ZMod (N+1)) k hy,if_pos rfl]
  have hi := characterProjection_inner_eq_zero N (upperBlock N)
    (n : ZMod (N+1)) (m : ZMod (N+1)) hnm
    (coefficientVector N f n y) (coefficientVector N f m y)
  rw [hfix n,hfix m] at hi
  unfold coefficientLoss complexLoss inversionTransfer
  simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,hi,
    upperProjection_coefficientVector N f s _ hy]
  by_cases hn : (n : ZMod (N+1))=s
  · have hm : (m : ZMod (N+1))≠s := fun h => hnm (hn.trans h.symm)
    simp only [if_neg hm,map_zero,inner_zero_right,sub_zero]
  · simp only [if_neg hn,map_zero,inner_zero_left,sub_zero]

/-- The actual infinite-tail arithmetic kernel of original coefficient pairs. -/
def tailLoss (n m : ℤ) (Y : ℝ) : ℂ := ∫ y in Ioi Y, coefficientLoss N r s f n m y

section Exceptional
variable (e : Ioo (0 : ℝ) (1/4))
    (g : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N+1))) (e : ℝ))

private theorem coefficient_norm_integrable (n : ℤ) {Y : ℝ} (hY : 0 < Y) :
    IntegrableOn (fun y => ‖coefficientVector N g n y‖^2) (Ioi Y) := by
  have h := integrable_finsetSum (Finset.univ : Finset (Deck N))
    (fun q _ => SelbergMaassBessel.mode_mass_integrable N e (quotientForm N g q) n hY)
  have he : (fun y => ‖coefficientVector N g n y‖^2)=
      fun y => ∑ q : Deck N, normSq (maassCoefficient N (quotientForm N g q) n y) := by
    funext y
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Complex.sq_norm,coefficientVector,WithLp.ofLp_toLp]
  rw [he]
  exact h

private theorem height_norm_integrable (n : ℤ) {Y : ℝ} (hY : 0 < Y) :
    IntegrableOn (fun y => ‖coefficientHeightVector N g n y‖^2) (Ioi Y) := by
  have h := integrable_finsetSum (Finset.univ : Finset (Deck N))
    (fun q _ => SelbergMaassBessel.mode_deriv_integrable N e (quotientForm N g q) n hY)
  have he : (fun y => ‖coefficientHeightVector N g n y‖^2)=
      fun y => ∑ q : Deck N, normSq (deriv (maassCoefficient N (quotientForm N g q) n) y) := by
    funext y
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Complex.sq_norm,coefficientHeightVector,WithLp.ofLp_toLp]
  rw [he]
  exact h

private theorem loss_integrable {u v : ℝ → EuclideanSpace ℂ (Deck N)} {Y : ℝ}
    (hu : ContinuousOn u (Ioi Y)) (hv : ContinuousOn v (Ioi Y))
    (hiu : IntegrableOn (fun y => ‖u y‖^2) (Ioi Y))
    (hiv : IntegrableOn (fun y => ‖v y‖^2) (Ioi Y)) :
    IntegrableOn (fun y => complexLoss N r s (u y) (v y)) (Ioi Y) := by
  let T := (inversionTransfer N r s).toContinuousLinearMap
  have hc : ContinuousOn (fun y => complexLoss N r s (u y) (v y)) (Ioi Y) :=
    (hu.inner hv).sub ((T.continuous.comp_continuousOn hu).inner (T.continuous.comp_continuousOn hv))
  exact (hiu.add hiv).mono' (hc.aestronglyMeasurable measurableSet_Ioi)
    (Filter.Eventually.of_forall (fun y => complexLoss_norm_le N r s (u y) (v y)))

private theorem coefficient_continuous {Y : ℝ} (hY : 0 < Y) (n : ℤ) :
    ContinuousOn (coefficientVector N g n) (Ioi Y) := fun _ hy =>
  (coefficientVector_hasDerivAt N g n (hY.trans hy)).continuousAt.continuousWithinAt

private theorem height_continuous {Y : ℝ} (hY : 0 < Y) (n : ℤ) :
    ContinuousOn (coefficientHeightVector N g n) (Ioi Y) := fun _ hy =>
  (coefficientHeightVector_hasDerivAt N g n (hY.trans hy)).continuousAt.continuousWithinAt

/-- The full mixed arithmetic coefficient kernel is genuinely integrable on the infinite cusp tail. -/
theorem coefficientLoss_integrable (n m : ℤ) {Y : ℝ} (hY : 0 < Y) :
    IntegrableOn (coefficientLoss N r s g n m) (Ioi Y) :=
  loss_integrable N r s (coefficient_continuous N e g hY n) (coefficient_continuous N e g hY m)
    (coefficient_norm_integrable N e g n hY) (coefficient_norm_integrable N e g m hY)

/-- Both original derivative slots in the mixed arithmetic current have finite absolute tail integral. -/
theorem coefficientWronskian_integrable (n m : ℤ) {Y : ℝ} (hY : 0 < Y) :
    IntegrableOn (coefficientWronskian N r s g n m) (Ioi Y) :=
  (loss_integrable N r s (height_continuous N e g hY n) (coefficient_continuous N e g hY m)
    (height_norm_integrable N e g n hY) (coefficient_norm_integrable N e g m hY)).sub
  (loss_integrable N r s (coefficient_continuous N e g hY n) (height_continuous N e g hY m)
    (coefficient_norm_integrable N e g n hY) (height_norm_integrable N e g m hY))

/-- The actual cross-frequency arithmetic current tends to zero; no outgoing endpoint is assumed. -/
theorem coefficientWronskian_tendsto_zero (n m : ℤ) :
    Filter.Tendsto (coefficientWronskian N r s g n m) Filter.atTop (nhds 0) :=
  tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi
    (fun _ hy => coefficientWronskian_hasDerivAt N r s g n m (lt_trans zero_lt_one hy))
    ((coefficientLoss_integrable N r s e g n m zero_lt_one).const_mul _)
    (coefficientWronskian_integrable N r s e g n m zero_lt_one)

/-- The boundary Wronskian equals the exact frequency difference times the full arithmetic tail kernel. -/
theorem coefficientWronskian_eq_tail (n m : ℤ) {Y : ℝ} (hY : 0 < Y) :
    coefficientWronskian N r s g n m Y=
      ((signedFrequency (N+1 : ℕ) m^2-signedFrequency (N+1 : ℕ) n^2 : ℝ) : ℂ)*
        tailLoss N r s g n m Y := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun y hy => coefficientWronskian_hasDerivAt N r s g n m (hY.trans_le hy))
    ((coefficientLoss_integrable N r s e g n m hY).const_mul _)
    (coefficientWronskian_tendsto_zero N r s e g n m)
  rw [integral_const_mul] at h
  simp only [Complex.ofReal_sub,zero_sub] at h ⊢
  change _=_*∫ y in Ioi Y, coefficientLoss N r s g n m y
  linear_combination h

/-- Distinct original residue channels cancel in the actual infinite-tail kernel. -/
theorem tailLoss_eq_zero_of_residue_ne (n m : ℤ)
    (hnm : (n : ZMod (N+1))≠(m : ZMod (N+1))) {Y : ℝ} (hY : 0 < Y) :
    tailLoss N r s g n m Y=0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  exact coefficientLoss_eq_zero_of_residue_ne N r s g n m hnm (hY.trans hy)

/-- Every same-frequency-square mixed current vanishes, including opposite original indices. -/
theorem coefficientWronskian_neg_eq_zero (n : ℤ) {Y : ℝ} (hY : 0 < Y) :
    coefficientWronskian N r s g n (-n) Y=0 := by
  rw [coefficientWronskian_eq_tail N r s e g n (-n) hY]
  have he : signedFrequency (N+1 : ℕ) (-n)^2=signedFrequency (N+1 : ℕ) n^2 := by
    simp only [signedFrequency,Int.cast_neg]
    ring
  rw [he,sub_self,Complex.ofReal_zero,zero_mul]

/-- The entire finite quadratic of the tail kernel is a literal integral of original source loss. -/
theorem tailLoss_quadratic (I : Finset ℤ) (a : ℤ → ℂ) {Y : ℝ} (hY : 0 < Y) :
    (∑ n ∈ I, ∑ m ∈ I, (starRingEnd ℂ) (a n)*a m*tailLoss N r s g n m Y)=
      ∫ y in Ioi Y, (lossEnergy N r s (∑ n ∈ I, a n • coefficientVector N g n y) : ℂ) := by
  have hi (n m : ℤ) := (coefficientLoss_integrable N r s e g n m hY).const_mul
    ((starRingEnd ℂ) (a n)*a m)
  have h := integral_finsetSum I (fun n _ => integrable_finsetSum I (fun m _ => hi n m))
  simp_rw [integral_finsetSum I (fun m _ => hi _ m),integral_const_mul] at h
  unfold tailLoss
  rw [← h]
  apply integral_congr_ae
  filter_upwards with y
  rw [← complexLoss_self,complexLoss_sum]
  rfl

/-- Full complex phase-sensitive positivity of the original infinite-tail coefficient Gram kernel. -/
theorem tailLoss_quadratic_nonneg (I : Finset ℤ) (a : ℤ → ℂ) {Y : ℝ} (hY : 0 < Y) :
    0 ≤ (∑ n ∈ I, ∑ m ∈ I, (starRingEnd ℂ) (a n)*a m*tailLoss N r s g n m Y).re := by
  rw [tailLoss_quadratic N r s e g I a hY,integral_complex_ofReal,Complex.ofReal_re]
  exact integral_nonneg (fun _ => lossEnergy_nonneg N r s _)

/-- The actual infinite-tail kernel is Hermitian, with its full complex phase. -/
theorem tailLoss_conj (n m : ℤ) (Y : ℝ) :
    (starRingEnd ℂ) (tailLoss N r s g n m Y)=tailLoss N r s g m n Y := by
  unfold tailLoss
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with y
  exact complexLoss_conj N r s _ _

/-- Every diagonal tail entry is the literal integral of nonnegative original transfer loss. -/
theorem tailLoss_self (n : ℤ) (Y : ℝ) :
    tailLoss N r s g n n Y=
      (∫ y in Ioi Y, lossEnergy N r s (coefficientVector N g n y) : ℝ) := by
  unfold tailLoss coefficientLoss
  simp_rw [complexLoss_self]
  rw [integral_complex_ofReal]

/-- Actual tail diagonal masses are nonnegative, including all zero-loss channels. -/
theorem tailLoss_self_nonneg (n : ℤ) (Y : ℝ) : 0 ≤ (tailLoss N r s g n n Y).re := by
  rw [tailLoss_self,Complex.ofReal_re]
  exact integral_nonneg (fun _ => lossEnergy_nonneg N r s _)

/-- A phase-sensitive Cauchy bound for every original off-diagonal infinite-tail Gram entry. -/
theorem tailLoss_norm_sq_le (n m : ℤ) {Y : ℝ} (hY : 0 < Y) :
    ‖tailLoss N r s g n m Y‖^2 ≤
      (tailLoss N r s g n n Y).re*(tailLoss N r s g m m Y).re := by
  classical
  let A := tailLoss N r s g n n Y
  let B := tailLoss N r s g n m Y
  let C := tailLoss N r s g m m Y
  have hAi : A.im=0 := by dsimp [A]; rw [tailLoss_self,Complex.ofReal_im]
  have hCi : C.im=0 := by dsimp [C]; rw [tailLoss_self,Complex.ofReal_im]
  have hC : 0 ≤ C.re := tailLoss_self_nonneg N r s e g m Y
  by_cases hnm : n=m
  · subst m
    change ‖A‖^2 ≤ A.re*A.re
    rw [Complex.sq_norm,Complex.normSq_apply,hAi]
    nlinarith
  · have hmn : m≠n := Ne.symm hnm
    have hquad (t : ℝ) : 0 ≤ A.re+2*normSq B*t+(normSq B*C.re)*t^2 := by
      let z : ℂ := (t : ℂ)*(starRingEnd ℂ) B
      have h := tailLoss_quadratic_nonneg N r s e g {n,m}
        (fun k => if k=n then (1 : ℂ) else z) hY
      simp only [Finset.sum_insert,Finset.mem_singleton,hnm,not_false_eq_true,
        Finset.sum_singleton,ite_true,if_neg hmn,map_one,one_mul,mul_one] at h
      have hb : tailLoss N r s g m n Y=(starRingEnd ℂ) B := (tailLoss_conj N r s e g n m Y).symm
      rw [hb] at h
      change 0 ≤ (A+z*B+((starRingEnd ℂ) z*(starRingEnd ℂ) B+(starRingEnd ℂ) z*z*C)).re at h
      convert h using 1
      simp only [Complex.add_re,Complex.mul_re,Complex.mul_im,Complex.conj_re,
        Complex.conj_im,z,Complex.ofReal_re,Complex.ofReal_im,Complex.normSq_apply,hCi]
      ring
    have h := sq_le_mul_of_quadratic_nonneg
      (mul_nonneg (Complex.normSq_nonneg B) hC) hquad
    change ‖B‖^2 ≤ A.re*C.re
    rw [Complex.sq_norm]
    have hB := Complex.normSq_nonneg B
    by_cases hz : normSq B=0
    · rw [hz]
      exact mul_nonneg (tailLoss_self_nonneg N r s e g n Y) hC
    · have hp : 0 < normSq B := lt_of_le_of_ne hB (Ne.symm hz)
      nlinarith

/-- Quantitative control of each actual mixed boundary current by its two original tail-loss masses. -/
theorem coefficientWronskian_norm_sq_le (n m : ℤ) {Y : ℝ} (hY : 0 < Y) :
    ‖coefficientWronskian N r s g n m Y‖^2 ≤
      (signedFrequency (N+1 : ℕ) m^2-signedFrequency (N+1 : ℕ) n^2)^2*
        ((tailLoss N r s g n n Y).re*(tailLoss N r s g m m Y).re) := by
  rw [coefficientWronskian_eq_tail N r s e g n m hY,norm_mul,mul_pow,
    Complex.norm_real,Real.norm_eq_abs,sq_abs]
  exact mul_le_mul_of_nonneg_left (tailLoss_norm_sq_le N r s e g n m hY) (sq_nonneg _)

end Exceptional

end
end GaloisForLFunctions.RHTower.SelbergMaassKernelWronskian
