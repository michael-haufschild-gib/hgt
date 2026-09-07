import GaloisForLFunctions.RHTower.EulerDeletionCompletedChronology
import GaloisForLFunctions.RHTower.DirichletUniformAbel
import GaloisForLFunctions.RHTower.Reflection

/-!
# Holomorphic realization of the literal deletion chronology

A locally summable Abel majorant supplies actual holomorphy of the full
complex finite part. Reflection and xi completion then give its exact
square-splitting equation, with the critical-line boundary energy retained.
-/
noncomputable section
open Filter Topology
open scoped BigOperators
namespace RHTower.DeletionHolomorphicChronology
open DeletionChronologicalLimit DeletionReflectedGram DeletionReflectedCurrent
open DeletionCompletedChronology DeletionJointCirculation

/-- The open critical strip, with neither boundary silently included. -/
def domain : Set ℂ := {s | 0<s.re ∧ s.re<1}

private theorem domain_open : IsOpen domain :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)

private theorem kernel_star (s : ℂ) (n : ℕ) :
    kernel (star s) n=star (kernel s n) := by
  simp only [kernel, ← Nat.cast_add_one, Complex.ofReal_natCast]
  simpa only [map_neg, Complex.star_def] using natCast_cpow_conj (n+1) (-s)

/-- The conjugated reflected kernel is holomorphic in the original parameter. -/
theorem star_kernel_partner (s : ℂ) (n : ℕ) :
    star (kernel (partner s) n)=kernel (1-s) n := by
  rw [← kernel_star]
  simp [partner]

private theorem differentiable_kernel (n : ℕ) : Differentiable ℂ (fun s => kernel s n) := by
  intro s
  have hn : ((((n:ℝ)+1:ℝ)):ℂ)≠0 := by exact_mod_cast (by positivity : (n:ℝ)+1≠0)
  exact DifferentiableAt.const_cpow (differentiable_id.neg s) (Or.inl hn)

/-- Each literal Abel remainder is entire; its conjugations cancel exactly. -/
theorem differentiable_abelRemainder (p n : ℕ) :
    Differentiable ℂ (fun s => abelRemainder p p s n) := by
  have hi : Differentiable ℂ (fun s => innerPrefix p s (n+1)) :=
    GaloisForLFunctions.RHTower.differentiable_dirichletPartialSum
      (eulerDeletionDirichletCoefficient p) (n+1)
  have h1 := (differentiable_kernel (n+1)).comp ((differentiable_const (c := (1:ℂ))).sub differentiable_id)
  have h0 := (differentiable_kernel n).comp ((differentiable_const (c := (1:ℂ))).sub differentiable_id)
  simpa only [abelRemainder, star_sub, star_kernel_partner, Function.comp_def, Pi.mul_apply, Pi.sub_apply, id_eq] using
    (hi.mul (h1.sub h0)).mul_const ((((n+1)%(p+1):ℕ):ℂ))

/-- Uniform Abel bound for every literal prefix, without any zero premise. -/
theorem norm_innerPrefix_le (p N : ℕ) {s : ℂ} (hs : 0<s.re) :
    ‖innerPrefix p s N‖ ≤ 2*p*(1+‖s‖/s.re) := by
  have h := GaloisForLFunctions.RHTower.norm_dirichletPartialSum_sub_le
    (eulerDeletionDirichletCoefficient_partialSum_norm_le p) hs (Nat.zero_le N)
  simpa only [GaloisForLFunctions.RHTower.dirichletPartialSum, Finset.range_zero,
    Finset.sum_empty, sub_zero, Nat.cast_zero, zero_add, Real.one_rpow, mul_one,
    innerPrefix, eulerDeletionWeightedJump] using h

private def box (δ R : ℝ) : Set ℂ := {s | δ<s.re ∧ s.re<1-δ ∧ ‖s‖<R}

private theorem box_open (δ R : ℝ) : IsOpen (box δ R) :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt Complex.continuous_re continuous_const).inter
      (isOpen_lt continuous_norm continuous_const))

/-- Explicit locally uniform summable majorant for the retained arithmetic remainder. -/
theorem norm_abelRemainder_le (p n : ℕ) {δ R : ℝ} (hδ : 0<δ) {s : ℂ}
    (hs : δ<s.re) (hs' : s.re<1-δ) (hR : ‖s‖<R) :
    ‖abelRemainder p p s n‖ ≤
      (2*p*(1+R/δ)*(1+R)*p)*((n:ℝ)+1)^(-1-δ) := by
  have hs0 : 0<s.re := hδ.trans hs
  have hr0 : 0<(partner s).re := by simp [partner]; linarith
  have hR0 : 0<R := (norm_nonneg s).trans_lt hR
  have hprefix : ‖innerPrefix p s (n+1)‖ ≤ 2*p*(1+R/δ) := by
    refine (norm_innerPrefix_le p (n+1) hs0).trans ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith [div_le_div₀ hR0.le hR.le hδ hs.le]
  have hpartner : ‖partner s‖ ≤ 1+R := by
    calc
      _ ≤ ‖(1:ℂ)‖+‖star s‖ := norm_sub_le _ _
      _ ≤ _ := by simpa using hR.le
  have hk : ‖kernel (partner s) (n+1)-kernel (partner s) n‖ ≤
      (1+R)*((n:ℝ)+1)^(-1-δ) := by
    have h := norm_cpow_shift_sub_le_of_nonneg (x := (n:ℝ)+1) (b := 1)
      (by positivity) zero_le_one hr0
    have h' : ‖kernel (partner s) (n+1)-kernel (partner s) n‖ ≤
      ‖partner s‖*((n:ℝ)+1)^(-(partner s).re-1) := by
      simpa only [kernel, Nat.cast_add, Nat.cast_one, mul_one] using h
    refine h'.trans (mul_le_mul hpartner ?_ (by positivity) (by positivity))
    apply Real.rpow_le_rpow_of_exponent_le (by have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n; linarith)
    simp only [partner, Complex.sub_re, Complex.one_re, Complex.star_def, Complex.conj_re]
    linarith
  have hp : (((n+1)%(p+1):ℕ):ℝ) ≤ p := by
    exact_mod_cast Nat.lt_succ_iff.mp (Nat.mod_lt (n+1) (Nat.succ_pos p))
  rw [abelRemainder, norm_mul, norm_mul, norm_star, Complex.norm_natCast]
  calc
    _ ≤ (2*p*(1+R/δ))*((1+R)*((n:ℝ)+1)^(-1-δ))*(p:ℝ) := by
      exact mul_le_mul (mul_le_mul hprefix hk (norm_nonneg _) (by positivity)) hp
        (by positivity) (by positivity)
    _ = _ := by ring

private theorem majorant_summable (p : ℕ) {δ R : ℝ} (hδ : 0<δ) :
    Summable (fun n : ℕ => (2*p*(1+R/δ)*(1+R)*p)*((n:ℝ)+1)^(-1-δ)) := by
  have h := Real.summable_nat_rpow.mpr (by linarith : -1-δ < -1)
  have h' := (summable_nat_add_iff (f := fun n : ℕ => (n:ℝ)^(-1-δ)) 1).2 h
  simpa only [Nat.cast_add, Nat.cast_one] using h'.mul_left (2*p*(1+R/δ)*(1+R)*p)

private theorem abelSum_differentiableOn_box (p : ℕ) {δ R : ℝ} (hδ : 0<δ) :
    DifferentiableOn ℂ (fun s => ∑' n, abelRemainder p p s n) (box δ R) := by
  apply Complex.differentiableOn_tsum_of_summable_norm (majorant_summable p hδ)
    (fun n => (differentiable_abelRemainder p n).differentiableOn) (box_open δ R)
  intro n s hs
  exact norm_abelRemainder_le p n hδ hs.1 hs.2.1 hs.2.2

private theorem exists_box {s : ℂ} (hs : s∈domain) :
    ∃ δ R : ℝ, 0<δ ∧ s∈box δ R := by
  refine ⟨min s.re (1-s.re)/2, ‖s‖+1, half_pos (lt_min hs.1 (sub_pos.mpr hs.2)), ?_⟩
  have h0 : 0 < min s.re (1-s.re) := lt_min hs.1 (sub_pos.mpr hs.2)
  have h1 := min_le_left s.re (1-s.re)
  have h2 := min_le_right s.re (1-s.re)
  exact ⟨by linarith, by linarith, by linarith⟩

/-- The actual Abel sum is holomorphic at every point of the open strip. -/
theorem differentiableAt_abelSum (p : ℕ) {s : ℂ} (hs : s∈domain) :
    DifferentiableAt ℂ (fun z => ∑' n, abelRemainder p p z n) s := by
  obtain ⟨δ,R,hδ,hbox⟩ := exists_box hs
  exact (abelSum_differentiableOn_box p hδ).differentiableAt ((box_open δ R).mem_nhds hbox)

/-- Differentiating the retained series is justified by its local summable majorant. -/
theorem hasSum_deriv_abelRemainder (p : ℕ) {s : ℂ} (hs : s∈domain) :
    HasSum (fun n => deriv (fun z => abelRemainder p p z n) s)
      (deriv (fun z => ∑' n, abelRemainder p p z n) s) := by
  obtain ⟨δ,R,hδ,hbox⟩ := exists_box hs
  exact Complex.hasSum_deriv_of_summable_norm (majorant_summable p hδ)
    (fun n => (differentiable_abelRemainder p n).differentiableOn) (box_open δ R)
    (fun n s hs => norm_abelRemainder_le p n hδ hs.1 hs.2.1 hs.2.2) hbox

/-- Two arbitrary strip parameters differ by the full actual Abel variation. -/
theorem chronologyLimit_sub (p : ℕ) {s t : ℂ} (hs : s∈domain) (ht : t∈domain) :
    chronologyLimit p s-chronologyLimit p t = -variationCurrent p p s t := by
  have h := (renormalizedPrefix_tendsto p hs.1 hs.2).sub (renormalizedPrefix_tendsto p ht.1 ht.2)
  exact tendsto_nhds_unique (h.congr (fun N => by simp [renormalizedPrefix]))
    (variationCurrent_tendsto p p hs.1 hs.2 ht.1 ht.2).2

/-- The real/imaginary presentation equals one holomorphic Abel sum plus a fixed constant. -/
theorem chronologyLimit_eq_abelSum (p : ℕ) {s : ℂ} (hs : s∈domain) :
    chronologyLimit p s = chronologyLimit p (1/2)+
      (∑' n, abelRemainder p p (1/2) n)-(∑' n, abelRemainder p p s n) := by
  have ht : (1/2:ℂ)∈domain := by norm_num [domain]
  have h := chronologyLimit_sub p hs ht
  rw [variationCurrent, Summable.tsum_sub
    (abelRemainder_summable_norm p p hs.1 hs.2).of_norm
    (abelRemainder_summable_norm p p ht.1 ht.2).of_norm] at h
  linear_combination h

/-- The full complex normalized chronology is holomorphic throughout the strip. -/
theorem analyticOnNhd_chronologyLimit (p : ℕ) : AnalyticOnNhd ℂ (chronologyLimit p) domain := by
  have hd : DifferentiableOn ℂ (chronologyLimit p) domain := by
    intro s hs
    have h := (differentiableAt_const (c := chronologyLimit p (1/2)+
      (∑' n, abelRemainder p p (1/2) n))).sub (differentiableAt_abelSum p hs)
    apply (h.congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [domain_open.mem_nhds hs] with z hz
    exact chronologyLimit_eq_abelSum p hz
  intro s hs
  exact hd.analyticAt (domain_open.mem_nhds hs)

private theorem domain_conj {s : ℂ} (hs : s∈domain) : star s∈domain := by
  simpa only [domain, Set.mem_setOf_eq, Complex.star_def, Complex.conj_re] using hs

private theorem domain_one_sub {s : ℂ} (hs : s∈domain) : 1-s∈domain := by
  change 0<(1-s).re ∧ (1-s).re<1
  simp only [Complex.sub_re, Complex.one_re]
  constructor <;> linarith [hs.1, hs.2]

private theorem jump_conj (p n : ℕ) (s : ℂ) :
    eulerDeletionWeightedJump p (star s) n=star (eulerDeletionWeightedJump p s n) := by
  change eulerDeletionDirichletCoefficient p n*kernel (star s) n =
    star (eulerDeletionDirichletCoefficient p n*kernel s n)
  rw [kernel_star, star_mul']
  simp [eulerDeletionDirichletCoefficient]

private theorem reflectedCross_conj (p N : ℕ) (s : ℂ) :
    reflectedCross p p (star s) N=star (reflectedCross p p s N) := by
  have hp : partner (star s)=star (partner s) := by simp [partner]
  simp only [reflectedCross, hp, chronologicalCrossPrefix, chronologicalCrossTerm,
    jump_conj]
  simp only [Complex.star_def, map_sum, map_mul, Complex.conj_conj]

private theorem renormalizedPrefix_conj (p N : ℕ) (s : ℂ) :
    renormalizedPrefix p (star s) N=star (renormalizedPrefix p s N) := by
  rw [renormalizedPrefix, renormalizedPrefix, reflectedCross_conj, star_add]
  congr 1
  simp [harmonicCounterterm]

/-- The full normalized arithmetic chronology retains the source's real structure. -/
theorem chronologyLimit_conj (p : ℕ) {s : ℂ} (hs : s∈domain) :
    chronologyLimit p (star s)=star (chronologyLimit p s) := by
  have hc := domain_conj hs
  exact tendsto_nhds_unique (renormalizedPrefix_tendsto p hc.1 hc.2)
    ((renormalizedPrefix_tendsto p hs.1 hs.2).star.congr
      (fun N => (renormalizedPrefix_conj p N s).symm))

private theorem endpoint_conj (p : ℕ) {s : ℂ} (hs : 0<s.re) :
    eulerDeletionDirichletSum p (star s)=star (eulerDeletionDirichletSum p s) := by
  have hc : 0<(star s).re := by simpa using hs
  exact tendsto_nhds_unique (source_endpoint_tendsto p hc)
    ((source_endpoint_tendsto p hs).star.congr (fun N => by
      simp only [endpoint]
      simp_rw [jump_conj]
      simp only [Complex.star_def, map_sum]))

/-- Holomorphic reflection equation with the entire endpoint product and arithmetic finite part. -/
theorem chronologyLimit_add_one_sub (p : ℕ) {s : ℂ} (hs : s∈domain) :
    chronologyLimit p s+chronologyLimit p (1-s)=
      eulerDeletionDirichletSum p s*eulerDeletionDirichletSum p (1-s)-
        (finitePart (p+1) (p+1):ℂ) := by
  have ht := domain_one_sub hs
  have hr : partner s∈domain := by simpa only [partner] using domain_one_sub (domain_conj hs)
  have he (N : ℕ) : renormalizedPrefix p s N+renormalizedPrefix p (1-s) N=
      symmetricCross p p s N+
        (DeletionReflectedGram.residue (p+1) (p+1)*(harmonic N:ℝ):ℂ) := by
    have hs' : 1-s=star (partner s) := by simp [partner]
    rw [renormalizedPrefix, renormalizedPrefix, hs', reflectedCross_conj]
    simp only [symmetricCross, reflectedCross, partner_partner, harmonicCounterterm,
      Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_mul]
    ring
  have h := tendsto_nhds_unique
    (((renormalizedPrefix_tendsto p hs.1 hs.2).add
      (renormalizedPrefix_tendsto p ht.1 ht.2)).congr he)
    (symmetricCross_harmonic_tendsto p p hs.1 hs.2)
  rw [← endpoint_conj p hr.1] at h
  simpa only [partner, star_sub, star_one, star_star] using h

private theorem dilationFactor_conj (p : ℕ) (s : ℂ) :
    complexEulerDilationFactor p (star s)=star (complexEulerDilationFactor p s) := by
  simp only [complexEulerDilationFactor, Complex.ofReal_natCast]
  rw [star_mul', star_natCast]
  congr 1
  simpa only [Complex.star_def, map_neg] using natCast_cpow_conj p (-s)

/-- The exact gamma/deletion completion preserves conjugation. -/
theorem xiFactor_conj (p : ℕ) (s : ℂ) : xiFactor p (star s)=star (xiFactor p s) := by
  rw [xiFactor, xiFactor, dilationFactor_conj]
  simp only [Complex.star_def, Gammaℝ_conj, map_div₀, map_mul, map_sub, map_one]

/-- The actual nontrivial-channel completion is holomorphic throughout the strip. -/
theorem differentiableAt_xiFactor {p : ℕ} (hp : 0<p) {s : ℂ} (hs : s∈domain) :
    DifferentiableAt ℂ (xiFactor p) s := by
  have hn : ((p+1:ℕ):ℂ)≠0 := by exact_mod_cast Nat.succ_ne_zero p
  have hpow := (DifferentiableAt.const_cpow (differentiable_id.neg s) (Or.inl hn)).const_mul
    ((p+1:ℕ):ℂ)
  have hnum : DifferentiableAt ℂ (fun z => z*(1-z)*Complex.Gammaℝ z) s :=
    (differentiableAt_id.mul ((differentiableAt_const (c := (1:ℂ))).sub
      differentiableAt_id)).mul (differentiableAt_Gammaℝ_of_re_pos hs.1)
  have hden : DifferentiableAt ℂ (fun z => 1-complexEulerDilationFactor (p+1) z) s :=
    (differentiableAt_const (c := (1:ℂ))).sub hpow
  exact hnum.div hden (one_sub_dilation_ne_zero (by omega) hs.2)

/-- The literal completed half of xi squared, retaining the arithmetic finite constant. -/
def completedSplit (p : ℕ) (s : ℂ) : ℂ :=
  xiFactor p s*xiFactor p (1-s)*(chronologyLimit p s+(finitePart (p+1) (p+1):ℂ)/2)

/-- The completed arithmetic half is holomorphic, not merely a pointwise splitting. -/
theorem analyticOnNhd_completedSplit {p : ℕ} (hp : 0<p) :
    AnalyticOnNhd ℂ (completedSplit p) domain := by
  have hd : DifferentiableOn ℂ (completedSplit p) domain := by
    intro s hs
    have h1 := (differentiableAt_xiFactor hp (domain_one_sub hs)).comp s
      ((differentiableAt_const (c := (1:ℂ))).sub differentiableAt_id)
    exact (((differentiableAt_xiFactor hp hs).mul h1).mul
      (((analyticOnNhd_chronologyLimit p) s hs).differentiableAt.add_const
        ((finitePart (p+1) (p+1):ℂ)/2))).differentiableWithinAt
  intro s hs
  exact hd.analyticAt (domain_open.mem_nhds hs)

/-- Exact real structure of the literal completed arithmetic half. -/
theorem completedSplit_conj (p : ℕ) {s : ℂ} (hs : s∈domain) :
    completedSplit p (star s)=star (completedSplit p s) := by
  have h1 : 1-star s=star (1-s) := by simp
  rw [completedSplit, completedSplit, h1, xiFactor_conj, xiFactor_conj,
    chronologyLimit_conj p hs]
  simp only [Complex.star_def, map_mul, map_add, map_div₀, map_ofNat, Complex.conj_ofReal]

/-- The two genuine arithmetic halves sum to xi squared throughout the strip. -/
theorem completedSplit_add_one_sub {p : ℕ} (hp : 0<p) {s : ℂ} (hs : s∈domain) :
    completedSplit p s+completedSplit p (1-s)=RiemannGaussian.riemannXi s^2 := by
  have ht := domain_one_sub hs
  have hsum := chronologyLimit_add_one_sub p hs
  have hF := xiFactor_mul_endpoint hp hs.1 hs.2
  have hFt := xiFactor_mul_endpoint hp ht.1 ht.2
  rw [RiemannGaussian.riemannXi_one_sub] at hFt
  simp only [completedSplit, sub_sub_cancel]
  calc
    _ = (xiFactor p s*eulerDeletionDirichletSum p s)*
      (xiFactor p (1-s)*eulerDeletionDirichletSum p (1-s)) := by
      linear_combination (xiFactor p s*xiFactor p (1-s))*hsum
    _ = _ := by rw [hF, hFt]; ring

/-- Boundary positivity is the norm square of the genuine completed endpoint. -/
theorem completedSplit_critical_energy {p : ℕ} (hp : 0<p) {s : ℂ} (hs : s.re=1/2) :
    2*(completedSplit p s).re=‖RiemannGaussian.riemannXi s‖^2 := by
  have hd : s∈domain := by
    change 0<s.re ∧ s.re<1
    rw [hs]
    norm_num
  have hr : 1-s=star s := by
    apply Complex.ext <;> norm_num [hs]
  have hxi : star (RiemannGaussian.riemannXi s)=RiemannGaussian.riemannXi s := by
    rw [← xiFactor_mul_endpoint hp hd.1 hd.2, star_mul', ← xiFactor_conj,
      ← endpoint_conj p hd.1, ← hr,
      xiFactor_mul_endpoint hp (domain_one_sub hd).1 (domain_one_sub hd).2,
      RiemannGaussian.riemannXi_one_sub]
    exact (xiFactor_mul_endpoint hp hd.1 hd.2).symm
  have h := completedSplit_add_one_sub hp hd
  rw [hr, completedSplit_conj p hd] at h
  have hn : ((‖RiemannGaussian.riemannXi s‖^2:ℝ):ℂ)=RiemannGaussian.riemannXi s^2 := by
    calc
      _ = RiemannGaussian.riemannXi s*star (RiemannGaussian.riemannXi s) := by
        simpa only [Complex.ofReal_pow, Complex.star_def] using
          (Complex.mul_conj' (RiemannGaussian.riemannXi s)).symm
      _ = _ := by rw [hxi]; ring
  have hre := congrArg Complex.re (h.trans hn.symm)
  simpa only [Complex.add_re, Complex.star_def, Complex.conj_re, Complex.ofReal_re,
    two_mul] using hre

/-- The proved completed source sign is on the critical boundary itself. -/
theorem completedSplit_critical_nonneg {p : ℕ} (hp : 0<p) {s : ℂ} (hs : s.re=1/2) :
    0 ≤ (completedSplit p s).re := by
  have h := completedSplit_critical_energy hp hs
  nlinarith [sq_nonneg ‖RiemannGaussian.riemannXi s‖]

/-- The analytic half retains exactly the original signed current and Abel phase at every zero. -/
theorem completedSplit_re_at_zero (p : ℕ) (rho : RiemannGaussian.NontrivialZetaZero) :
    2*(completedSplit p rho.1).re =
      -(xiPhase p rho.1).re*(reflectionCurrent p rho.1).re-
        2*(xiPhase p rho.1).im*abelPhase p rho.1 := by
  have hk : xiFactor p rho.1*xiFactor p (1-rho.1)=xiPhase p rho.1 := by
    rw [xiPhase, ← xiFactor_conj]
    simp only [partner, star_sub, star_one, star_star]
  rw [completedSplit, hk, chronologyLimit_at_zero p rho]
  simp [Complex.mul_re, Complex.mul_im]
  ring

end RHTower.DeletionHolomorphicChronology
end
