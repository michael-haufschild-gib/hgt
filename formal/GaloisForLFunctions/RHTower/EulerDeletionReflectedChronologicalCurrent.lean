import GaloisForLFunctions.RHTower.EulerDeletionReflectedLogarithmicGram
import GaloisForLFunctions.RHTower.DirichletAbel

/-!
# The actual reflected chronological variation current

The arithmetic diagonal cancels at every cutoff when the parameter changes.
The surviving variation is an absolutely summable source current, with a
quantitative all-cutoff certificate at every actual nontrivial zero.
-/

noncomputable section
open Filter Topology
open scoped BigOperators
namespace RHTower.DeletionReflectedCurrent
open DeletionChronologicalLimit DeletionReflectedGram

/-- The actual chronological cross prefix with the reflected outer exponent. -/
def reflectedCross (p q : ℕ) (s : ℂ) (N : ℕ) : ℂ :=
  chronologicalCrossPrefix (eulerDeletionWeightedJump p s)
    (eulerDeletionWeightedJump q (partner s)) N

/-- The full Abel remainder, with the actual weighted inner prefix and outer residue. -/
def abelRemainder (p q : ℕ) (s : ℂ) (n : ℕ) : ℂ :=
  innerPrefix p s (n+1)*star (kernel (partner s) (n+1)-kernel (partner s) n)*
    (((n+1) % (q+1):ℕ):ℂ)

/-- The actual terminal term, including the incomplete outer residue. -/
def terminal (p q : ℕ) (s : ℂ) (N : ℕ) : ℂ :=
  outerTest p s (partner s) (N-1)*((N % (q+1):ℕ):ℂ)

/-- The source current comparing two reflected parameters, before any zero specialization. -/
def variationCurrent (p q : ℕ) (s t : ℂ) : ℂ :=
  ∑' n, (abelRemainder p q s n-abelRemainder p q t n)

/-- The full diagonal chronological current across the critical-line reflection. -/
def reflectionCurrent (p : ℕ) (s : ℂ) : ℂ := variationCurrent p p s (partner s)

@[simp] theorem partner_partner (s : ℂ) : partner (partner s)=s := by
  simp [partner]

private theorem partner_re (s : ℂ) : (partner s).re=1-s.re := by simp [partner]

private theorem star_weight (s : ℂ) (n : ℕ) :
    star ((n:ℂ)^(-s)) = (n:ℂ)^(-star s) := by
  have h := (Complex.cpow_conj (n:ℂ) (-s)
    (by simpa only [Complex.natCast_arg] using Real.pi_pos.ne)).symm
  simpa only [Complex.star_def, map_natCast, map_neg] using h

/-- The reflected scalar weight is exactly harmonic, independently of the parameter. -/
theorem kernel_reflected_pair (s : ℂ) (n : ℕ) :
    kernel s n*star (kernel (partner s) n) = (((n+1:ℕ):ℂ))⁻¹ := by
  have hn : ((n+1:ℕ):ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  simp only [kernel, ← Nat.cast_add_one, Complex.ofReal_natCast]
  rw [star_weight, ← Complex.cpow_add _ _ hn]
  have he : -s + -star (partner s) = (-1:ℂ) := by
    simp only [partner, star_sub, star_one, star_star]
    ring
  rw [he, Complex.cpow_neg_one]

/-- Finite Abel decomposition retains the whole common arithmetic term and terminal boundary. -/
theorem reflectedCross_abel (p q N : ℕ) (s : ℂ) :
    reflectedCross p q s N = terminal p q s N -
      (∑ n ∈ Finset.range (N-1),
        coprimeAbelCoefficient (p+1) (q+1) (n+1)/((n+1:ℕ):ℂ)) -
      ∑ n ∈ Finset.range (N-1), abelRemainder p q s n := by
  let A (N : ℕ) : ℂ := ((N % (q+1):ℕ):ℂ)
  have hA (N : ℕ) : ∑ n ∈ Finset.range N, eulerDeletionDirichletCoefficient q n = A N :=
    eulerDeletionDirichletCoefficient_partialSum q N
  have hab := Finset.sum_range_by_parts (outerTest p s (partner s))
    (eulerDeletionDirichletCoefficient q) N
  simp only [smul_eq_mul, hA] at hab
  have hleft : reflectedCross p q s N =
      ∑ n ∈ Finset.range N, outerTest p s (partner s) n*eulerDeletionDirichletCoefficient q n := by
    unfold reflectedCross chronologicalCrossPrefix
    apply Finset.sum_congr rfl
    intro n _
    have ha : star (eulerDeletionDirichletCoefficient q n) =
        eulerDeletionDirichletCoefficient q n := by simp [eulerDeletionDirichletCoefficient]
    change innerPrefix p s n*star (eulerDeletionDirichletCoefficient q n*kernel (partner s) n) = _
    rw [star_mul', ha]
    simp only [outerTest]
    ring
  rw [hleft, hab]
  have hinc (n : ℕ) :
      (outerTest p s (partner s) (n+1)-outerTest p s (partner s) n)*A (n+1) =
        coprimeAbelCoefficient (p+1) (q+1) (n+1)/((n+1:ℕ):ℂ)+
          abelRemainder p q s n := by
    rw [outerTest_increment]
    change (eulerDeletionDirichletCoefficient p n*kernel s n*star (kernel (partner s) n)+
      innerPrefix p s (n+1)*star (kernel (partner s) (n+1)-kernel (partner s) n))*A (n+1) = _
    rw [mul_assoc (eulerDeletionDirichletCoefficient p n), kernel_reflected_pair]
    simp only [coprimeAbelCoefficient, eulerDeletionDirichletCoefficient, abelRemainder, A]
    ring
  simp_rw [hinc]
  rw [Finset.sum_add_distrib]
  dsimp [terminal, A]
  ring

/-- Parameter variation cancels the full arithmetic term even when moduli share factors. -/
theorem reflectedCross_sub (p q N : ℕ) (s t : ℂ) :
    reflectedCross p q s N-reflectedCross p q t N =
      terminal p q s N-terminal p q t N-
        ∑ n ∈ Finset.range (N-1), (abelRemainder p q s n-abelRemainder p q t n) := by
  rw [reflectedCross_abel, reflectedCross_abel, Finset.sum_sub_distrib]
  ring

/-- The retained source remainder is absolutely summable everywhere in the open strip. -/
theorem abelRemainder_summable_norm (p q : ℕ) {s : ℂ}
    (hs : 0<s.re) (hs' : s.re<1) : Summable (fun n => ‖abelRemainder p q s n‖) := by
  exact (outerTest_remainder_summable p q s (partner s) hs
    (by rw [partner_re]; linarith)).norm

/-- Every retained terminal term vanishes on the open strip, without a zero premise. -/
theorem terminal_tendsto (p q : ℕ) {s : ℂ} (hs : 0<s.re) (hs' : s.re<1) :
    Tendsto (terminal p q s) atTop (nhds 0) := by
  have ht := ((outerTest_tendsto_zero p s (partner s) hs
    (by rw [partner_re]; linarith)).comp (Filter.tendsto_sub_atTop_nat 1)).norm.mul_const (q:ℝ)
  apply squeeze_zero_norm' (Filter.Eventually.of_forall (fun N => ?_)) (by simpa using ht)
  rw [terminal, norm_mul, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left
    (by exact_mod_cast Nat.lt_succ_iff.mp (Nat.mod_lt N (Nat.succ_pos q))) (norm_nonneg _)

/-- The variation limit is an actual absolutely summable arithmetic current. -/
theorem variationCurrent_tendsto (p q : ℕ) {s t : ℂ}
    (hs : 0<s.re) (hs' : s.re<1) (ht : 0<t.re) (ht' : t.re<1) :
    Summable (fun n => ‖abelRemainder p q s n-abelRemainder p q t n‖) ∧
      Tendsto (fun N => reflectedCross p q s N-reflectedCross p q t N) atTop
        (nhds (-variationCurrent p q s t)) := by
  have hsum := (abelRemainder_summable_norm p q hs hs').of_norm.sub
    (abelRemainder_summable_norm p q ht ht').of_norm
  refine ⟨hsum.norm, ?_⟩
  have hc := hsum.hasSum.tendsto_sum_nat.comp (Filter.tendsto_sub_atTop_nat 1)
  have hb := (terminal_tendsto p q hs hs').sub (terminal_tendsto p q ht ht')
  simpa only [sub_self, zero_sub, variationCurrent] using
    (hb.sub hc).congr (fun N => (reflectedCross_sub p q N s t).symm)

/-- Reflection reverses the full complex current. -/
theorem reflectionCurrent_partner (p : ℕ) (s : ℂ) :
    reflectionCurrent p (partner s) = -reflectionCurrent p s := by
  simp only [reflectionCurrent, variationCurrent, partner_partner, ← tsum_neg]
  congr 1
  funext n
  ring

/-- The reflected current vanishes identically on the critical line. -/
theorem reflectionCurrent_of_re_half (p : ℕ) {s : ℂ} (hs : s.re=1/2) :
    reflectionCurrent p s=0 := by
  have hp : partner s=s := by
    apply Complex.ext
    · simp [partner, hs]
      ring
    · simp [partner]
  simp [reflectionCurrent, variationCurrent, hp]

/-- The imaginary current is the exact endpoint-product response, with no discarded diagonal. -/
theorem reflectionCurrent_im (p : ℕ) {s : ℂ} (hs : 0<s.re) (hs' : s.re<1) :
    (reflectionCurrent p s).im =
      -(eulerDeletionDirichletSum p s*star (eulerDeletionDirichletSum p (partner s))).im := by
  have hv0 := (variationCurrent_tendsto p p (s := s) (t := partner s) hs hs'
    (by rw [partner_re]; linarith) (by rw [partner_re]; linarith)).2
  have hv := (Complex.imCLM.continuous.tendsto _).comp hv0
  have he (N : ℕ) : (reflectedCross p p s N-reflectedCross p p (partner s) N).im =
      (symmetricCross p p s N+(DeletionReflectedGram.residue (p+1) (p+1)*(harmonic N:ℝ):ℂ)).im := by
    simp [reflectedCross, symmetricCross, partner_partner, sub_eq_add_neg]
  have hc := (Complex.imCLM.continuous.tendsto _).comp
    (symmetricCross_harmonic_tendsto p p hs hs')
  have hu := tendsto_nhds_unique (hv.congr he) hc
  change (-variationCurrent p p s (partner s)).im =
    (eulerDeletionDirichletSum p s*star (eulerDeletionDirichletSum p (partner s))-
      (finitePart (p+1) (p+1):ℂ)).im at hu
  simp only [Complex.neg_im, Complex.sub_im, Complex.ofReal_im, sub_zero] at hu
  change -(reflectionCurrent p s).im = _ at hu
  linarith

/-- Every actual nontrivial zero forces the imaginary arithmetic current to vanish. -/
theorem reflectionCurrent_im_at_nontrivial_zero (p : ℕ)
    (rho : RiemannGaussian.NontrivialZetaZero) : (reflectionCurrent p rho.1).im=0 := by
  rw [reflectionCurrent_im p (RiemannGaussian.NontrivialZetaZero.zero_lt_re rho)
    (RiemannGaussian.NontrivialZetaZero.re_lt_one rho),
    DeletionJointCirculation.source_endpoint_value p
      (RiemannGaussian.NontrivialZetaZero.zero_lt_re rho) rho.2.2.2,
    rho.2.1, mul_zero, zero_mul, Complex.zero_im, neg_zero]


/-- Explicit inverse-square coefficient for a zero's actual Abel remainder. -/
def tailConstant (p q : ℕ) (s : ℂ) : ℝ :=
  eulerDeletionAbelTailConstant p s*q*‖partner s‖

/-- At an actual zero, the retained remainder gains a full inverse-square majorant. -/
theorem norm_abelRemainder_at_nontrivial_zero (p q : ℕ)
    (rho : RiemannGaussian.NontrivialZetaZero) (n : ℕ) :
    ‖abelRemainder p q rho.1 n‖ ≤ tailConstant p q rho.1/((n:ℝ)+1)^2 := by
  have hs := RiemannGaussian.NontrivialZetaZero.zero_lt_re rho
  have hr : 0<(partner rho.1).re := by
    rw [partner_re]
    linarith [RiemannGaussian.NontrivialZetaZero.re_lt_one rho]
  have hA : 0≤eulerDeletionAbelTailConstant p rho.1 := by
    unfold eulerDeletionAbelTailConstant
    positivity
  have hP := norm_eulerDeletionWeightedJump_prefix_le_of_zeta_zero
    p (n+1) hs rho.2.2.2 rho.2.1
  have hP' : ‖innerPrefix p rho.1 (n+1)‖ ≤
      eulerDeletionAbelTailConstant p rho.1*((n:ℝ)+1)^(-rho.1.re) := by
    refine hP.trans (mul_le_mul_of_nonneg_left ?_ hA)
    apply Real.rpow_le_rpow_of_nonpos (by positivity) (by push_cast; linarith) (by linarith)
  have hD : ‖kernel (partner rho.1) (n+1)-kernel (partner rho.1) n‖ ≤
      ‖partner rho.1‖*((n:ℝ)+1)^(-(partner rho.1).re-1) := by
    have hd := norm_cpow_shift_sub_le_of_nonneg (x := (n:ℝ)+1) (b := 1)
      (by positivity) zero_le_one hr
    simpa only [kernel, Nat.cast_add, Nat.cast_one, mul_one] using hd
  have hq : (((n+1)%(q+1):ℕ):ℝ) ≤ q := by
    exact_mod_cast Nat.lt_succ_iff.mp (Nat.mod_lt (n+1) (Nat.succ_pos q))
  rw [abelRemainder, norm_mul, norm_mul, norm_star, Complex.norm_natCast]
  calc
    _ ≤ (eulerDeletionAbelTailConstant p rho.1*((n:ℝ)+1)^(-rho.1.re))*
        (‖partner rho.1‖*((n:ℝ)+1)^(-(partner rho.1).re-1))*(q:ℝ) := by
      apply mul_le_mul (mul_le_mul hP' hD (norm_nonneg _) (by positivity)) hq
        (by positivity) (by positivity)
    _ = tailConstant p q rho.1*(((n:ℝ)+1)^(-rho.1.re)*
        ((n:ℝ)+1)^(-(partner rho.1).re-1)) := by unfold tailConstant; ring
    _ = tailConstant p q rho.1*((n:ℝ)+1)^(-2:ℝ) := by
      rw [← Real.rpow_add (by positivity), partner_re]
      congr 2
      ring
    _ = _ := by rw [Real.rpow_neg (by positivity), Real.rpow_two]; rfl

private theorem inverse_square_step {x : ℝ} (hx : 1≤x) :
    1/x^2 ≤ 2*(1/x-1/(x+1)) := by
  have hx0 : 0<x := by linarith
  have hx1 : 0<x+1 := by linarith
  rw [div_le_iff₀ (sq_pos_of_pos hx0)]
  field_simp
  nlinarith

private theorem norm_tsum_sub_prefix_le {f : ℕ → ℂ} {K : ℝ}
    (hK : 0≤K) (hf : Summable f) (hb : ∀n, ‖f n‖ ≤ K/((n:ℝ)+1)^2) (N : ℕ) :
    ‖(∑' n, f n)-(∑ n ∈ Finset.range N, f n)‖ ≤ 2*K/((N:ℝ)+1) := by
  let g (n : ℕ) : ℝ := 2*K/((n+N:ℕ)+1:ℕ)
  have hstep (n : ℕ) : K/((n+N:ℕ)+1:ℕ)^2 ≤ g n-g (n+1) := by
    have h := mul_le_mul_of_nonneg_left
      (inverse_square_step (x := ((n+N:ℕ):ℝ)+1)
        (by have hn : 0≤((n+N:ℕ):ℝ) := Nat.cast_nonneg _; linarith)) hK
    dsimp only [g]
    convert h using 1 <;> push_cast <;> first | rfl | ring
  have hfinite (M : ℕ) : ‖∑ n ∈ Finset.range M, f (n+N)‖ ≤ 2*K/((N:ℝ)+1) := by
    calc
      _ ≤ ∑ n ∈ Finset.range M, ‖f (n+N)‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.range M, (g n-g (n+1)) := by
        apply Finset.sum_le_sum
        intro n _
        exact (hb (n+N)).trans (by simpa only [Nat.cast_add, Nat.cast_one] using hstep n)
      _ = g 0-g M := Finset.sum_range_sub' g M
      _ ≤ _ := by
        have hn : 0≤g M := by dsimp [g]; positivity
        simpa [g] using sub_le_self (g 0) hn
  have ht := ((summable_nat_add_iff (f := f) N).2 hf).hasSum.tendsto_sum_nat.norm
  have htail := le_of_tendsto ht (Filter.Eventually.of_forall hfinite)
  rw [← hf.sum_add_tsum_nat_add N, add_sub_cancel_left]
  exact htail

/-- The actual remainder has an explicit inverse-linear tail at every nontrivial zero. -/
theorem abelRemainder_tail_at_nontrivial_zero (p q : ℕ)
    (rho : RiemannGaussian.NontrivialZetaZero) (N : ℕ) :
    ‖(∑' n, abelRemainder p q rho.1 n)-
      (∑ n ∈ Finset.range N, abelRemainder p q rho.1 n)‖ ≤
        2*tailConstant p q rho.1/((N:ℝ)+1) := by
  have hs := RiemannGaussian.NontrivialZetaZero.zero_lt_re rho
  apply norm_tsum_sub_prefix_le
    (by unfold tailConstant eulerDeletionAbelTailConstant; positivity)
    (abelRemainder_summable_norm p q hs
      (RiemannGaussian.NontrivialZetaZero.re_lt_one rho)).of_norm
    (norm_abelRemainder_at_nontrivial_zero p q rho)

/-- Complete complex reflection-current error, with both actual zero tails retained. -/
theorem variationCurrent_tail_at_nontrivial_zero (p q : ℕ)
    (rho : RiemannGaussian.NontrivialZetaZero) (N : ℕ) :
    ‖variationCurrent p q rho.1 (partner rho.1)-
      (∑ n ∈ Finset.range N, (abelRemainder p q rho.1 n-
        abelRemainder p q (partner rho.1) n))‖ ≤
      2*(tailConstant p q rho.1+tailConstant p q (partner rho.1))/((N:ℝ)+1) := by
  let r := RiemannGaussian.NontrivialZetaZero.conjugatePartner rho
  have hre : r.1 = partner rho.1 := rfl
  have hnorm := (variationCurrent_tendsto p q
    (RiemannGaussian.NontrivialZetaZero.zero_lt_re rho)
    (RiemannGaussian.NontrivialZetaZero.re_lt_one rho)
    (s := rho.1) (t := partner rho.1)
    (by rw [← hre]; exact RiemannGaussian.NontrivialZetaZero.zero_lt_re r)
    (by rw [← hre]; exact RiemannGaussian.NontrivialZetaZero.re_lt_one r)).1
  apply norm_tsum_sub_prefix_le
    (by unfold tailConstant eulerDeletionAbelTailConstant; rw [← hre];
        have hr := RiemannGaussian.NontrivialZetaZero.zero_lt_re r
        have hs := RiemannGaussian.NontrivialZetaZero.zero_lt_re rho
        positivity) hnorm.of_norm
  intro n
  calc
    _ ≤ ‖abelRemainder p q rho.1 n‖+‖abelRemainder p q (partner rho.1) n‖ := norm_sub_le _ _
    _ ≤ tailConstant p q rho.1/((n:ℝ)+1)^2+
        tailConstant p q (partner rho.1)/((n:ℝ)+1)^2 := by
      exact add_le_add (norm_abelRemainder_at_nontrivial_zero p q rho n)
        (by simpa only [hre] using norm_abelRemainder_at_nontrivial_zero p q r n)
    _ = _ := by ring

/-- Every finite imaginary-current prefix at an actual zero fits its certified remaining tail. -/
theorem imaginary_prefix_bound_at_nontrivial_zero (p : ℕ)
    (rho : RiemannGaussian.NontrivialZetaZero) (N : ℕ) :
    |(∑ n ∈ Finset.range N, (abelRemainder p p rho.1 n-
      abelRemainder p p (partner rho.1) n)).im| ≤
        2*(tailConstant p p rho.1+tailConstant p p (partner rho.1))/((N:ℝ)+1) := by
  have he := Complex.abs_im_le_norm
    (variationCurrent p p rho.1 (partner rho.1)-
      (∑ n ∈ Finset.range N, (abelRemainder p p rho.1 n-
        abelRemainder p p (partner rho.1) n)))
  change |(reflectionCurrent p rho.1).im-_| ≤ _ at he
  rw [reflectionCurrent_im_at_nontrivial_zero, zero_sub, abs_neg] at he
  exact he.trans (variationCurrent_tail_at_nontrivial_zero p p rho N)

end RHTower.DeletionReflectedCurrent
