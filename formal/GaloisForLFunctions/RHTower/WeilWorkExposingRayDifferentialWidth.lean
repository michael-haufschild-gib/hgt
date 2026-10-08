import GaloisForLFunctions.RHTower.WeilWorkExposingRayDifferentialParity
import GaloisForLFunctions.RHTower.WeilWorkExposingRayTailAsymptotic

/-!
# Translation width and differential synthesis of the literal exposing ray

Every fixed finite list of actual Riemann-kernel derivatives has a uniform
full-theta envelope under bounded translations and arbitrary complex synthesis.
At translation width below two, its complete integer atom trace is exponentially
smaller than the literal exposing ray unless the coefficient budget grows
exponentially. This remains true for arbitrary finite signed mixtures and
independent row centers. The budget is homogeneous under source/weight rescaling.

The proof controls the whole complex autocorrelation and its integrability.
Packets are not assumed or asserted compact or polar. The result includes finite
polar derivative/translation filters but supplies no archimedean energy sign,
no bound uniform in derivative order, and no solution of the WP02 lower inequality.

Paper: docs/reports/weil-work/results/02-exposing-ray/DIFFERENTIAL-WIDTH-PROOF.md.
-/

open MeasureTheory Real Set Filter Topology Zeta23
open scoped ComplexConjugate
noncomputable section
namespace RHTower.ExposingRayWidth
open ExposingRayDifferential

/-- Finite complex synthesis of actual Riemann derivatives. -/
def packet {ι : Type*} [Fintype ι] (k : ι → ℕ) (c : ι → ℂ) (x : ι → ℝ) (t : ℝ) : ℂ :=
  ∑ j,c j * riemannKernelDeriv (k j) (t-x j)

private theorem packet_continuous {ι : Type*} [Fintype ι]
    (k : ι → ℕ) (c : ι → ℂ) (x : ι → ℝ) : Continuous (packet k c x) := by
  unfold packet
  apply continuous_finsetSum
  intro j _
  exact continuous_const.mul ((continuous_riemannKernelDeriv (k j)).comp
    (continuous_id.sub continuous_const))

/-- A uniform envelope: derivative orders are fixed, coefficients and translations are free. -/
theorem packet_envelope {ι : Type*} [Fintype ι]
    (k : ι → ℕ) {R a : ℝ} (ha : 0 < a) (haπ : a < π) :
    ∃ B : ℝ, 0 < B ∧ ∀ (c : ι → ℂ) (x : ι → ℝ), (∀ j, |x j| ≤ R) → ∀ t : ℝ,
      ‖packet k c x t‖ ≤ (B*(∑ j,‖c j‖))*
        exp (-(a*exp (-(2*R))*exp (2*|t|)))*exp (-|t|) := by
  classical
  choose B hB hu using fun j => kernel_derivative_upper_subcritical (k j) ha haπ
  let H := 1+∑ j,B j
  have hsum : 0 ≤ ∑ j,B j := Finset.sum_nonneg fun j _ => (hB j).le
  have hH : 0 < H := by dsimp [H]; linarith
  have hBH (j : ι) : B j ≤ H := by
    have h := Finset.single_le_sum (s:=Finset.univ) (f:=B)
      (fun j _ => (hB j).le) (Finset.mem_univ j)
    dsimp [H]; linarith
  refine ⟨exp R*H, by positivity, fun c x hx t => ?_⟩
  have hshift (j : ι) : ‖riemannKernelDeriv (k j) (t-x j)‖ ≤
      (H*exp R)*exp (-(a*exp (-(2*R))*exp (2*|t|)))*exp (-|t|) := by
    have ht : |t|-R ≤ |t-x j| := by
      have hh : |t| ≤ |t-x j|+|x j| := by
        simpa using (abs_add_le (t-x j) (x j))
      linarith [hx j]
    have he : exp (-(2*R))*exp (2*|t|) ≤ exp (2*|t-x j|) := by
      rw [← exp_add]; apply exp_le_exp.mpr; linarith
    have he1 : exp (-(a*exp (2*|t-x j|))) ≤
        exp (-(a*exp (-(2*R))*exp (2*|t|))) := by
      apply exp_le_exp.mpr; nlinarith
    have he2 : exp (-|t-x j|) ≤ exp R*exp (-|t|) := by
      rw [← exp_add]; exact exp_le_exp.mpr (by linarith)
    calc _ ≤ B j*exp (-(a*exp (2*|t-x j|)))*exp (-|t-x j|) := hu j _
      _ ≤ H*exp (-(a*exp (-(2*R))*exp (2*|t|)))*(exp R*exp (-|t|)) := by gcongr; exact hBH j
      _ = _ := by ring
  have hsumc : 0 ≤ ∑ j,‖c j‖ := Finset.sum_nonneg fun j _ => norm_nonneg _
  calc ‖packet k c x t‖ ≤ ∑ j, ‖c j*riemannKernelDeriv (k j) (t-x j)‖ := norm_sum_le _ _
    _ = ∑ j, ‖c j‖*‖riemannKernelDeriv (k j) (t-x j)‖ := by
      simp only [norm_mul]
    _ ≤ ∑ j, ‖c j‖*((H*exp R)*exp (-(a*exp (-(2*R))*exp (2*|t|)))*exp (-|t|)) := by
      apply Finset.sum_le_sum; intro j _; exact mul_le_mul_of_nonneg_left (hshift j) (norm_nonneg _)
    _ = (exp R*H*(∑ j,‖c j‖))*exp (-(a*exp (-(2*R))*exp (2*|t|)))*exp (-|t|) := by
      simp only [Finset.mul_sum,Finset.sum_mul]; apply Finset.sum_congr rfl; intro j _; ring

private theorem exp_pair (t y : ℝ) :
    2*exp |y| ≤ exp (2*|t|)+exp (2*|t-y|) := by
  have htri : |y| ≤ |t|+|t-y| := calc
    |y| = |t-(t-y)| := by congr 1; ring
    _ ≤ _ := abs_sub _ _
  have he := exp_le_exp.mpr htri
  rw [exp_add] at he
  have h1 : exp (2*|t|) = exp |t|^2 := by rw [show 2*|t| = |t|+|t| by ring,exp_add,sq]
  have h2 : exp (2*|t-y|) = exp |t-y|^2 := by
    rw [show 2*|t-y| = |t-y|+|t-y| by ring,exp_add,sq]
  rw [h1,h2]
  nlinarith [sq_nonneg (exp |t|-exp |t-y|)]

private theorem correlation_pointwise {f : ℝ → ℂ} {B a : ℝ}
    (hB : 0 ≤ B) (ha : 0 < a)
    (hu : ∀ t, ‖f t‖ ≤ B*exp (-(a*exp (2*|t|)))*exp (-|t|)) (t y : ℝ) :
    ‖f t*conj (f (t-y))‖ ≤ B^2*exp (-(2*a*exp |y|))*exp (-|t|) := by
  rw [norm_mul,Complex.norm_conj]
  have he : exp (-(a*exp (2*|t|)))*exp (-(a*exp (2*|t-y|))) ≤
      exp (-(2*a*exp |y|)) := by
    rw [← exp_add]; apply exp_le_exp.mpr; nlinarith [exp_pair t y]
  have hs : exp (-|t-y|) ≤ 1 := exp_le_one_iff.mpr (by linarith [abs_nonneg (t-y)])
  calc _ ≤ (B*exp (-(a*exp (2*|t|)))*exp (-|t|))*
        (B*exp (-(a*exp (2*|t-y|)))*exp (-|t-y|)) :=
      mul_le_mul (hu t) (hu (t-y)) (norm_nonneg _) (by positivity)
    _ = B^2*(exp (-(a*exp (2*|t|)))*exp (-(a*exp (2*|t-y|))))*
        exp (-|t|)*exp (-|t-y|) := by ring
    _ ≤ B^2*exp (-(2*a*exp |y|))*exp (-|t|)*1 := by gcongr
    _ = _ := by ring

private theorem correlation_bound {f : ℝ → ℂ} {B a : ℝ}
    (hB : 0 ≤ B) (ha : 0 < a) (hf : Continuous f)
    (hu : ∀ t, ‖f t‖ ≤ B*exp (-(a*exp (2*|t|)))*exp (-|t|)) (y : ℝ) :
    Integrable (fun t => f t*conj (f (t-y))) ∧
      ‖EF.weilTest f f y‖ ≤ 2*B^2*exp (-(2*a*exp |y|)) := by
  have hb := correlation_pointwise hB ha hu
  have hg := integrable_exp_neg_abs.const_mul (B^2*exp (-(2*a*exp |y|)))
  have hi : Integrable (fun t => f t*conj (f (t-y))) := by
    apply hg.mono'
      (hf.mul (Complex.continuous_conj.comp (hf.comp (continuous_id.sub continuous_const)))).aestronglyMeasurable
    exact Eventually.of_forall fun t => hb t y
  refine ⟨hi, ?_⟩
  have h := norm_integral_le_of_norm_le hg (Eventually.of_forall fun t => hb t y)
  rw [integral_const_mul,integral_exp_neg_abs] at h
  unfold EF.weilTest convolution EF.tilde
  simp only [ContinuousLinearMap.mul_apply']
  simp_rw [show ∀ t : ℝ, -(y-t)=t-y from fun t => by ring]
  exact h.trans_eq (by ring)

/-- Complete integer-trace bound, uniform in coefficients and translation positions. -/
theorem packet_atom_bound {ι : Type*} [Fintype ι]
    (k : ι → ℕ) {R a : ℝ} (ha : 0 < a) (haπ : a < π) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : ι → ℂ) (x : ι → ℝ), (∀ j, |x j| ≤ R) →
      ∀ n : ℕ, 1 ≤ n → |atomCoeff (packet k c x) n| ≤
        C*(∑ j,‖c j‖)^2*exp (-(2*a*exp (-(2*R))*n)) := by
  obtain ⟨B,hB,hu⟩ := packet_envelope k (R:=R) ha haπ
  refine ⟨4*B^2, by positivity, fun c x hx n hn => ?_⟩
  have hsumc : 0 ≤ ∑ j,‖c j‖ := Finset.sum_nonneg fun j _ => norm_nonneg _
  have hBc : 0 ≤ B*(∑ j,‖c j‖) := by positivity
  have hb := correlation_bound hBc (mul_pos ha (exp_pos _))
    (packet_continuous k c x) (hu c x hx)
  have h1 := (hb (log n)).2
  have h2 := (hb (-log n)).2
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hlog : 0 ≤ log (n:ℝ) := log_nonneg (by exact_mod_cast hn)
  rw [abs_of_nonneg hlog, exp_log hn0] at h1
  rw [abs_neg,abs_of_nonneg hlog, exp_log hn0] at h2
  calc _ ≤ ‖EF.weilTest (packet k c x) (packet k c x) (log n)+
        EF.weilTest (packet k c x) (packet k c x) (-log n)‖ := Complex.abs_re_le_norm _
    _ ≤ ‖EF.weilTest (packet k c x) (packet k c x) (log n)‖+
        ‖EF.weilTest (packet k c x) (packet k c x) (-log n)‖ := norm_add_le _ _
    _ ≤ 4*(B*(∑ j,‖c j‖))^2*exp (-(2*(a*exp (-(2*R)))*n)) := by linarith
    _ = _ := by ring_nf


/-- Subcritical translation width gives uniform exponential separation from the literal ray. -/
theorem packet_relative_bound {ι : Type*} [Fintype ι]
    (k : ι → ℕ) {R : ℝ} (hR : R < 1) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (c : ι → ℂ) (x : ι → ℝ), (∀ j, |x j| ≤ R) →
        |atomCoeff (packet k c x) n| ≤
          C*(∑ j,‖c j‖)^2*exp (-(δ*n))*exposingWeight n := by
  let a := π*exp (R-1)
  have ha : 0 < a := mul_pos pi_pos (exp_pos _)
  have haπ : a < π := by
    have h := exp_lt_one_iff.mpr (show R-1<0 by linarith)
    dsimp [a]; nlinarith [Real.pi_pos]
  let s := 2*a*exp (-(2*R))
  have hs : exposingWeightDecayRate < s := by
    have he : exp (-2) < exp (-(R+1)) := exp_lt_exp.mpr (by linarith)
    have heq : s = 2*π*exp (-(R+1)) := by
      dsimp [s,a]
      rw [show 2*(π*exp (R-1))*exp (-(2*R)) =
        2*π*(exp (R-1)*exp (-(2*R))) by ring,← exp_add]
      congr 2; ring
    rw [heq]; unfold exposingWeightDecayRate
    exact mul_lt_mul_of_pos_left he (by positivity)
  let r := (exposingWeightDecayRate+s)/2
  have hr : exposingWeightDecayRate < r := by dsimp [r]; linarith
  have hrs : r < s := by dsimp [r]; linarith
  obtain ⟨C,hC,hup⟩ := packet_atom_bound k (R:=R) ha haπ
  obtain ⟨D,hD,hlo⟩ := exposingWeight_exponential_lower hr
  refine ⟨C/D,s-r,by positivity,by linarith,?_⟩
  filter_upwards [hlo,eventually_ge_atTop (1:ℕ)] with n hn hn1
  intro c x hx
  have h := hup c x hx n hn1
  have heq : C*(∑ j,‖c j‖)^2*exp (-(s*n)) =
      ((C/D)*(∑ j,‖c j‖)^2*exp (-((s-r)*n)))*(D*exp (-(r*n))) := by
    rw [show ((C/D)*(∑ j,‖c j‖)^2*exp (-((s-r)*n)))*(D*exp (-(r*n))) =
      ((C/D)*D)*(∑ j,‖c j‖)^2*(exp (-((s-r)*n))*exp (-(r*n))) by ring]
    rw [div_mul_cancel₀ _ hD.ne',← exp_add]
    congr 2; ring
  change |atomCoeff (packet k c x) n| ≤ C*(∑ j,‖c j‖)^2*exp (-(s*n)) at h
  rw [heq] at h
  exact h.trans (mul_le_mul_of_nonneg_left hn (by positivity))

/-- Matching late exposing coefficients forces exponential coefficient amplification,
uniformly over every position choice within a fixed subcritical translation window. -/
theorem packet_matching_amplification {ι : Type*} [Fintype ι]
    (k : ι → ℕ) {R : ℝ} (hR : R < 1) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (c : ι → ℂ) (x : ι → ℝ), (∀ j, |x j| ≤ R) →
        exposingWeight n ≤ |atomCoeff (packet k c x) n| →
          exp (δ*n) ≤ C*(∑ j,‖c j‖)^2 := by
  obtain ⟨C,δ,hC,hδ,h⟩ := packet_relative_bound k hR
  refine ⟨C,δ,hC,hδ,?_⟩
  filter_upwards [h,exposingWeight_eventually_pos] with n hn hwn
  intro c x hx hmatch
  have hb := hmatch.trans (hn c x hx)
  have hratio : 1 ≤ C*(∑ j,‖c j‖)^2*exp (-(δ*n)) := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hratio (exp_pos (δ*n)).le
  have he : exp (-(δ*n))*exp (δ*n)=1 := by rw [← exp_add]; simp
  simpa only [one_mul,mul_assoc,he,mul_one] using hm

private theorem exponential_gap {a b P : ℝ} (hab : a < b) (hP : 0 < P) (Q : ℝ) :
    ∀ᶠ n : ℕ in atTop, Q*exp (-(b*n)) ≤ P*exp (-(a*n)) := by
  let q := exp (-(b-a))
  have hq0 : 0 ≤ q := (exp_pos _).le
  have hq1 : q < 1 := exp_lt_one_iff.mpr (by linarith)
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul Q
  have he : ∀ᶠ n : ℕ in atTop, Q*q^n < P := ht.eventually_lt_const (by simpa using hP)
  filter_upwards [he] with n hn
  have heq : Q*exp (-(b*n)) = (Q*q^n)*exp (-(a*n)) := by
    dsimp [q]; rw [← exp_nat_mul,mul_assoc,← exp_add]; congr 2; ring
  rw [heq]
  exact mul_le_mul_of_nonneg_right hn.le (exp_pos _).le

/-- Every fixed finite synthesis of subcritical width is negligible against the exposing ray. -/
theorem packet_negligible {ι : Type*} [Fintype ι]
    (k : ι → ℕ) (c : ι → ℂ) (x : ι → ℝ) {R : ℝ}
    (hx : ∀ j, |x j| ≤ R) (hR : R < 1) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      |atomCoeff (packet k c x) n| ≤ ε*exposingWeight n := by
  obtain ⟨C,δ,hC,hδ,h⟩ := packet_relative_bound k hR
  intro ε hε
  have he := exponential_gap (a:=0) hδ hε (C*(∑ j,‖c j‖)^2)
  filter_upwards [h,he,exposingWeight_eventually_pos] with n hn he hnpos
  simp only [zero_mul,neg_zero,exp_zero,mul_one] at he
  exact (hn c x hx).trans (mul_le_mul_of_nonneg_right he hnpos.le)


/-- Uniform separation for arbitrary finite signed mixtures over the fixed derivative basis.
The coefficient budget retains the absolute weight of every row. -/
theorem mixture_relative_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    (k : ι → ℕ) {R : ℝ} (hR : R < 1) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (α : κ → ℝ) (c : κ → ι → ℂ) (x : κ → ι → ℝ),
        (∀ i j, |x i j| ≤ R) →
        |∑ i, α i*atomCoeff (packet k (c i) (x i)) n| ≤
          C*(∑ i, |α i| *(∑ j,‖c i j‖)^2)*exp (-(δ*n))*exposingWeight n := by
  obtain ⟨C,δ,hC,hδ,h⟩ := packet_relative_bound k hR
  refine ⟨C,δ,hC,hδ,?_⟩
  filter_upwards [h] with n hn
  intro α c x hx
  calc _ ≤ ∑ i, |α i*atomCoeff (packet k (c i) (x i)) n| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |α i| *|atomCoeff (packet k (c i) (x i)) n| := by simp only [abs_mul]
    _ ≤ ∑ i, |α i| *(C*(∑ j,‖c i j‖)^2*exp (-(δ*n))*exposingWeight n) := by
      apply Finset.sum_le_sum; intro i _
      exact mul_le_mul_of_nonneg_left (hn (c i) (x i) (hx i)) (abs_nonneg _)
    _ = _ := by
      simp only [Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl; intro i _; ring

/-- Exact late-ray matching forces exponential growth of the full finite-mixture budget. -/
theorem mixture_matching_amplification {ι κ : Type*} [Fintype ι] [Fintype κ]
    (k : ι → ℕ) {R : ℝ} (hR : R < 1) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (α : κ → ℝ) (c : κ → ι → ℂ) (x : κ → ι → ℝ),
        (∀ i j, |x i j| ≤ R) →
        exposingWeight n ≤ |∑ i, α i*atomCoeff (packet k (c i) (x i)) n| →
          exp (δ*n) ≤ C*(∑ i, |α i| *(∑ j,‖c i j‖)^2) := by
  obtain ⟨C,δ,hC,hδ,h⟩ := mixture_relative_bound (κ:=κ) k hR
  refine ⟨C,δ,hC,hδ,?_⟩
  filter_upwards [h,exposingWeight_eventually_pos] with n hn hwn
  intro α c x hx hmatch
  have hb := hmatch.trans (hn α c x hx)
  have hratio : 1 ≤ C*(∑ i, |α i| *(∑ j,‖c i j‖)^2)*exp (-(δ*n)) := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hratio (exp_pos (δ*n)).le
  have he : exp (-(δ*n))*exp (δ*n)=1 := by rw [← exp_add]; simp
  simpa only [one_mul,mul_assoc,he,mul_one] using hm

/-- Every fixed finite mixture in a subcritical translation window is negligible. -/
theorem mixture_negligible {ι κ : Type*} [Fintype ι] [Fintype κ]
    (k : ι → ℕ) (α : κ → ℝ) (c : κ → ι → ℂ) (x : κ → ι → ℝ) {R : ℝ}
    (hx : ∀ i j, |x i j| ≤ R) (hR : R < 1) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      |∑ i, α i*atomCoeff (packet k (c i) (x i)) n| ≤ ε*exposingWeight n := by
  obtain ⟨C,δ,hC,hδ,h⟩ := mixture_relative_bound (κ:=κ) k hR
  intro ε hε
  have he := exponential_gap (a:=0) hδ hε (C*(∑ i, |α i| *(∑ j,‖c i j‖)^2))
  filter_upwards [h,he,exposingWeight_eventually_pos] with n hn he hnpos
  simp only [zero_mul,neg_zero,exp_zero,mul_one] at he
  exact (hn α c x hx).trans (mul_le_mul_of_nonneg_right he hnpos.le)

/-- No nonzero fixed multiple of the literal exposing ray is an eventual trace of such a mixture. -/
theorem mixture_not_proportional {ι κ : Type*} [Fintype ι] [Fintype κ]
    (k : ι → ℕ) (α : κ → ℝ) (c : κ → ι → ℂ) (x : κ → ι → ℝ) {R : ℝ}
    (hx : ∀ i j, |x i j| ≤ R) (hR : R < 1) (q : ℝ) (hq : q ≠ 0) :
    ¬ ∀ᶠ n : ℕ in atTop,
      (∑ i, α i*atomCoeff (packet k (c i) (x i)) n) = q*exposingWeight n := by
  intro heq
  have hqpos := abs_pos.mpr hq
  have hsmall := mixture_negligible k α c x hx hR (|q|/2) (by positivity)
  obtain ⟨n,he,hs,hw⟩ := (heq.and (hsmall.and exposingWeight_eventually_pos)).exists
  rw [he,abs_mul,abs_of_pos hw] at hs
  nlinarith


private theorem atomCoeff_translate (f : ℝ → ℂ) (s : ℝ) (n : ℕ) :
    atomCoeff (fun t => f (t-s)) n = atomCoeff f n := by
  have ht (y : ℝ) : EF.weilTest (fun t => f (t-s)) (fun t => f (t-s)) y = EF.weilTest f f y := by
    unfold EF.weilTest convolution EF.tilde
    simp only [ContinuousLinearMap.mul_apply']
    simp_rw [show ∀ t : ℝ, -(y-t)-s=(t-s)-y from fun t => by ring,
      show ∀ t : ℝ, -(y-t)=t-y from fun t => by ring]
    exact integral_sub_right_eq_self (fun t => f t*conj (f (t-y))) s
  unfold atomCoeff
  rw [ht,ht]

/-- Only relative translation width matters; common motion of a row does not change its trace. -/
theorem packet_atom_recenter {ι : Type*} [Fintype ι]
    (k : ι → ℕ) (c : ι → ℂ) (x : ι → ℝ) (s : ℝ) (n : ℕ) :
    atomCoeff (packet k c x) n = atomCoeff (packet k c (fun j => x j-s)) n := by
  have he : (fun t => packet k c (fun j => x j-s) (t-s)) = packet k c x := by
    funext t
    unfold packet
    apply Finset.sum_congr rfl
    intro j _
    rw [show (t-s)-(x j-s)=t-x j by ring]
  rw [← he,atomCoeff_translate]

/-- The amplification law holds for arbitrary row centers, not only centered windows. -/
theorem mixture_window_amplification {ι κ : Type*} [Fintype ι] [Fintype κ]
    (k : ι → ℕ) {R : ℝ} (hR : R < 1) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (α : κ → ℝ) (c : κ → ι → ℂ) (x : κ → ι → ℝ) (s : κ → ℝ),
        (∀ i j, |x i j-s i| ≤ R) →
        exposingWeight n ≤ |∑ i, α i*atomCoeff (packet k (c i) (x i)) n| →
          exp (δ*n) ≤ C*(∑ i, |α i| *(∑ j,‖c i j‖)^2) := by
  obtain ⟨C,δ,hC,hδ,h⟩ := mixture_matching_amplification (κ:=κ) k hR
  refine ⟨C,δ,hC,hδ,?_⟩
  filter_upwards [h] with n hn
  intro α c x s hx hm
  apply hn α c (fun i j => x i j-s i) hx
  have he : (∑ i, α i*atomCoeff (packet k (c i) (fun j => x i j-s i)) n) =
      ∑ i, α i*atomCoeff (packet k (c i) (x i)) n := by
    apply Finset.sum_congr rfl
    intro i _
    rw [packet_atom_recenter k (c i) (x i) (s i) n]
  rw [he]
  exact hm

end RHTower.ExposingRayWidth
