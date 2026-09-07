import GaloisForLFunctions.RHTower.EulerDeletionHolomorphicChronology
import GaloisForLFunctions.RHTower.RiemannGaussian.FiniteToEntireRealApproximation
import GaloisForLFunctions.RHTower.ArithmeticJointJetExclusion

/-!
# Multiplicity-sensitive horizontal contact of completed deletion chronology

The exact reflected pair has the contact of xi squared. Odd critical
multiplicity forces negative nearby source values, even though the entire
critical boundary energy is nonnegative. The full contact law is retained.
-/
noncomputable section
open Filter Topology Set
namespace RHTower.DeletionHorizontalContact
open DeletionHolomorphicChronology RiemannGaussian

/-- Both actual horizontal real parts, with neither orientation discarded. -/
def horizontalPair (p : ℕ) (rho : ℂ) (d : ℝ) : ℝ :=
  (completedSplit p (rho+(d:ℂ))).re+(completedSplit p (rho-(d:ℂ))).re

private theorem shift_domain {rho : ℂ} (hr : rho.re=1/2) {d : ℝ}
    (hd : 0<d) (hd' : d<1/2) :
    rho+(d:ℂ)∈domain ∧ rho-(d:ℂ)∈domain := by
  simp only [domain, Set.mem_setOf_eq, Complex.add_re, Complex.sub_re, Complex.ofReal_re, hr]
  constructor <;> constructor <;> linarith

private theorem reflected_shift {rho : ℂ} (hr : rho.re=1/2) (d : ℝ) :
    1-(rho+(d:ℂ))=star (rho-(d:ℂ)) := by
  apply Complex.ext <;> norm_num [hr]
  all_goals ring

/-- The full finite horizontal pair is exactly the real part of genuine xi squared. -/
theorem horizontalPair_eq_xi_sq {p : ℕ} (hp : 0<p) {rho : ℂ} (hr : rho.re=1/2)
    {d : ℝ} (hd : 0<d) (hd' : d<1/2) :
    horizontalPair p rho d=(RiemannGaussian.riemannXi (rho+(d:ℂ))^2).re := by
  have hs := shift_domain hr hd hd'
  have h := completedSplit_add_one_sub hp hs.1
  rw [reflected_shift hr d, completedSplit_conj p hs.2] at h
  simpa only [horizontalPair, Complex.add_re, Complex.star_def, Complex.conj_re] using
    congrArg Complex.re h

/-- Every nontrivial deletion modulus has exactly the same reflected horizontal pair. -/
theorem horizontalPair_channel_independent {p q : ℕ} (hp : 0<p) (hq : 0<q)
    {rho : ℂ} (hr : rho.re=1/2) {d : ℝ} (hd : 0<d) (hd' : d<1/2) :
    horizontalPair p rho d=horizontalPair q rho d := by
  rw [horizontalPair_eq_xi_sq hp hr hd hd', horizontalPair_eq_xi_sq hq hr hd hd']

private theorem xi_horizontal_reflection {rho : ℂ} (hr : rho.re=1/2) (d : ℝ) :
    RiemannGaussian.riemannXi (rho-(d:ℂ))=star (RiemannGaussian.riemannXi (rho+(d:ℂ))) := by
  have he : rho-(d:ℂ)=1-star (rho+(d:ℂ)) := by
    apply Complex.ext <;> norm_num [hr]
    all_goals ring
  rw [he, riemannXi_one_sub]
  simpa only [Complex.star_def] using riemannXi_conj (rho+(d:ℂ))

private theorem shift_tendsto (rho : ℂ) :
    Tendsto (fun d : ℝ => rho+(d:ℂ)) (𝓝[>] 0) (𝓝 rho) := by
  have h : Tendsto (fun d : ℝ => rho+(d:ℂ)) (𝓝 (0:ℝ)) (𝓝 (rho+(0:ℂ))) :=
    (continuous_const.add Complex.continuous_ofReal).tendsto 0
  simpa only [Complex.ofReal_zero, add_zero] using
    h.mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))

private theorem neg_shift_tendsto (rho : ℂ) :
    Tendsto (fun d : ℝ => rho-(d:ℂ)) (𝓝[>] 0) (𝓝 rho) := by
  have h : Tendsto (fun d : ℝ => rho-(d:ℂ)) (𝓝 (0:ℝ)) (𝓝 (rho-(0:ℂ))) :=
    (continuous_const.sub Complex.continuous_ofReal).tendsto 0
  simpa only [Complex.ofReal_zero, sub_zero] using
    h.mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))

private theorem leading_phase {rho : ℂ} (hr : rho.re=1/2) {m : ℕ} {g : ℂ→ℂ}
    (hg : ContinuousAt g rho)
    (hf : RiemannGaussian.riemannXi =ᶠ[𝓝 rho] fun z => (z-rho)^m*g z) :
    star (g rho)=(-1:ℂ)^m*g rho := by
  have hp := hg.tendsto.comp (shift_tendsto rho)
  have hm := hg.tendsto.comp (neg_shift_tendsto rho)
  have he : ∀ᶠ d : ℝ in 𝓝[>] 0,
      star (g (rho+(d:ℂ)))=(-1:ℂ)^m*g (rho-(d:ℂ)) := by
    filter_upwards [(shift_tendsto rho).eventually hf,
      (neg_shift_tendsto rho).eventually hf,
      (self_mem_nhdsWithin : ∀ᶠ d : ℝ in 𝓝[>] 0, 0<d)] with d hp hm hd
    have hd0 : (d:ℂ)≠0 := by exact_mod_cast hd.ne'
    have h := xi_horizontal_reflection hr d
    rw [hp, hm] at h
    have hm0 : rho-(d:ℂ)-rho=-(d:ℂ) := by ring
    rw [hm0, add_sub_cancel_left] at h
    have hcancel : (d:ℂ)^m*((-1:ℂ)^m*g (rho-(d:ℂ))) =
        (d:ℂ)^m*star (g (rho+(d:ℂ))) := by
      calc
        _ = (-(d:ℂ))^m*g (rho-(d:ℂ)) := by rw [neg_pow]; ring
        _ = _ := by
          simpa only [star_mul', star_pow, Complex.star_def, Complex.conj_ofReal] using h
    exact (mul_left_cancel₀ (pow_ne_zero m hd0) hcancel).symm
  exact tendsto_nhds_unique (hp.star.congr' he) (hm.const_mul ((-1:ℂ)^m))

private theorem leading_square_re {m : ℕ} {c : ℂ} (hc : star c=(-1:ℂ)^m*c) :
    (c^2).re=(-1:ℝ)^m*‖c‖^2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  rcases Nat.even_or_odd m with hm | hm
  · have hi := congrArg Complex.im hc
    simp only [hm.neg_one_pow, one_mul, Complex.star_def, Complex.conj_im] at hi
    have hz : c.im=0 := by linarith
    simp only [hm.neg_one_pow, one_mul, pow_two, Complex.mul_re,
      hz]
    ring
  · have hr := congrArg Complex.re hc
    simp only [hm.neg_one_pow, neg_one_mul, Complex.star_def, Complex.conj_re,
      Complex.neg_re] at hr
    have hz : c.re=0 := by linarith
    simp only [hm.neg_one_pow, neg_one_mul, pow_two, Complex.mul_re,
      hz]
    ring

private theorem quotient_tendsto {rho : ℂ} {m : ℕ} {g : ℂ→ℂ}
    (hg : ContinuousAt g rho)
    (hf : RiemannGaussian.riemannXi =ᶠ[𝓝 rho] fun z => (z-rho)^m*g z) :
    Tendsto (fun d : ℝ => RiemannGaussian.riemannXi (rho+(d:ℂ))/(d:ℂ)^m) (𝓝[>] 0) (𝓝 (g rho)) := by
  apply (hg.tendsto.comp (shift_tendsto rho)).congr'
  filter_upwards [(shift_tendsto rho).eventually hf,
    (self_mem_nhdsWithin : ∀ᶠ d : ℝ in 𝓝[>] 0, 0<d)] with d hf hd
  have hd0 : (d:ℂ)≠0 := by exact_mod_cast hd.ne'
  change g (rho+(d:ℂ))=RiemannGaussian.riemannXi (rho+(d:ℂ))/(d:ℂ)^m
  rw [hf, add_sub_cancel_left]
  field_simp

private theorem contact_of_factor {p : ℕ} (hp : 0<p) {rho : ℂ} (hr : rho.re=1/2)
    {m : ℕ} {g : ℂ→ℂ} (hg : ContinuousAt g rho)
    (hf : RiemannGaussian.riemannXi =ᶠ[𝓝 rho] fun z => (z-rho)^m*g z) :
    Tendsto (fun d : ℝ => horizontalPair p rho d/d^(2*m)) (𝓝[>] 0)
      (𝓝 ((-1:ℝ)^m*‖g rho‖^2)) := by
  have h := (Complex.continuous_re.tendsto _).comp ((quotient_tendsto hg hf).pow 2)
  rw [leading_square_re (leading_phase hr hg hf)] at h
  apply h.congr'
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1/2)] with d hd
  rw [horizontalPair_eq_xi_sq hp hr hd.1 hd.2]
  change ((RiemannGaussian.riemannXi (rho+(d:ℂ))/(d:ℂ)^m)^2).re = _
  rw [div_pow, ← pow_mul, Nat.mul_comm m 2, ← Complex.ofReal_pow, Complex.div_ofReal_re]

/-- Every actual critical zero has a nonzero contact magnitude and its full multiplicity parity. -/
theorem exists_horizontal_contact
    (rho : NontrivialZetaZero) (hr : rho.1.re=1/2) :
    ∃ B : ℝ, 0<B ∧ ∀ p : ℕ, 0<p →
      Tendsto (fun d : ℝ => horizontalPair p rho.1 d/d^(2*analyticZetaZeroMultiplicity rho))
        (𝓝[>] 0) (𝓝 ((-1:ℝ)^(analyticZetaZeroMultiplicity rho)*B)) := by
  have hnt : analyticOrderAt RiemannGaussian.riemannXi rho.1≠⊤ := by
    rw [analyticOrderAt_riemannXi_eq_riemannZeta]
    exact analyticOrderAt_riemannZeta_nontrivialZero_ne_top rho
  obtain ⟨g,hg,hg0,hf⟩ := (analyticAt_riemannXi rho.1).analyticOrderAt_ne_top.mp hnt
  simp only [smul_eq_mul] at hf
  have hf' : RiemannGaussian.riemannXi =ᶠ[𝓝 rho.1] fun z =>
      (z-rho.1)^(analyticZetaZeroMultiplicity rho)*g z := by
    simpa only [analyticZetaZeroMultiplicity, analyticOrderNatAt,
      analyticOrderAt_riemannXi_eq_riemannZeta] using hf
  refine ⟨‖g rho.1‖^2, sq_pos_of_pos (norm_pos_iff.mpr hg0), ?_⟩
  intro p hp
  exact contact_of_factor hp hr hg.continuousAt hf'

/-- Odd critical multiplicity gives one quantitative negative neighborhood for every nontrivial modulus. -/
theorem odd_contact_negative (rho : NontrivialZetaZero)
    (hr : rho.1.re=1/2) (hm : Odd (analyticZetaZeroMultiplicity rho)) :
    ∃ B ε : ℝ, 0<B ∧ 0<ε ∧ ∀ p : ℕ, 0<p → ∀ d : ℝ, 0<d → d<ε →
      horizontalPair p rho.1 d ≤ -B/2*d^(2*analyticZetaZeroMultiplicity rho) := by
  obtain ⟨B,hB,hall⟩ := exists_horizontal_contact rho hr
  have h := hall 1 (by norm_num)
  rw [hm.neg_one_pow, neg_one_mul] at h
  have he := h.eventually (eventually_lt_nhds (by linarith : -B < -B/2))
  obtain ⟨ε,hε,he⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp he
  refine ⟨B,min ε (1/2),hB,lt_min hε (by norm_num),fun p hp d hd hd' => ?_⟩
  have hdε := lt_of_lt_of_le hd' (min_le_left ε (1/2:ℝ))
  have hdhalf := lt_of_lt_of_le hd' (min_le_right ε (1/2:ℝ))
  rw [horizontalPair_channel_independent hp (by norm_num : 0<1) hr hd hdhalf]
  exact ((div_lt_iff₀ (pow_pos hd _)).mp (he ⟨hd,hdε⟩)).le

/-- Even critical multiplicity has one strictly positive contact neighborhood for every nontrivial modulus. -/
theorem even_contact_positive (rho : NontrivialZetaZero)
    (hr : rho.1.re=1/2) (hm : Even (analyticZetaZeroMultiplicity rho)) :
    ∃ B ε : ℝ, 0<B ∧ 0<ε ∧ ∀ p : ℕ, 0<p → ∀ d : ℝ, 0<d → d<ε →
      B/2*d^(2*analyticZetaZeroMultiplicity rho) ≤ horizontalPair p rho.1 d := by
  obtain ⟨B,hB,hall⟩ := exists_horizontal_contact rho hr
  have h := hall 1 (by norm_num)
  rw [hm.neg_one_pow, one_mul] at h
  have he := h.eventually (eventually_gt_nhds (by linarith : B/2 < B))
  obtain ⟨ε,hε,he⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp he
  refine ⟨B,min ε (1/2),hB,lt_min hε (by norm_num),fun p hp d hd hd' => ?_⟩
  have hdε := lt_of_lt_of_le hd' (min_le_left ε (1/2:ℝ))
  have hdhalf := lt_of_lt_of_le hd' (min_le_right ε (1/2:ℝ))
  rw [horizontalPair_channel_independent hp (by norm_num : 0<1) hr hd hdhalf]
  exact ((lt_div_iff₀ (pow_pos hd _)).mp (he ⟨hd,hdε⟩)).le

/-- The unconditional simple-critical census supplies actual multiplicity-one centers above every height. -/
theorem exists_high_simple_center (T : ℝ) :
    ∃ rho : NontrivialZetaZero, T<rho.1.im ∧ rho.1.re=1/2 ∧
      analyticZetaZeroMultiplicity rho=1 := by
  obtain ⟨t,hT,ht,hz,hm⟩ := DeletionMixedRefinement.exists_high_simple_critical_xi T
  let z := DeletionMixedRefinement.criticalResponsePoint t
  have hline : z.re=1/2 := by simp [z, DeletionMixedRefinement.criticalResponsePoint]
  have hs : 0<z.re ∧ z.re<1 := by rw [hline]; norm_num
  have hzeta : riemannZeta z=0 := (xi_zero_iff_zeta_zero_of_mem_strip hs.1 hs.2).mp hz
  have htriv : ¬∃ n : ℕ, z=-2*(n+1) := by
    rintro ⟨n,he⟩
    have h := congrArg Complex.re he
    norm_num [hline] at h
    have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
    nlinarith
  have hz1 : z≠1 := by intro he; have h := congrArg Complex.re he; rw [hline] at h; norm_num at h
  let rho : NontrivialZetaZero := ⟨z,hzeta,htriv,hz1⟩
  refine ⟨rho, ?_, hline, ?_⟩
  · simpa [rho, z, DeletionMixedRefinement.criticalResponsePoint] using hT
  · change (analyticOrderAt riemannZeta z).toNat=1
    rw [← xi_analyticOrderAt_eq_riemannZeta_of_mem_strip hs]
    exact hm

/-- Every nontrivial channel has negative off-line source values above every height. -/
theorem exists_high_negative_source {p : ℕ} (hp : 0<p) (T : ℝ) :
    ∃ s : ℂ, s∈domain ∧ T<s.im ∧ s.re≠1/2 ∧ (completedSplit p s).re<0 := by
  obtain ⟨rho,hT,hr,hm⟩ := exists_high_simple_center T
  obtain ⟨B,ε,hB,hε,hneg⟩ := odd_contact_negative rho hr (by rw [hm]; exact ⟨0, by norm_num⟩)
  let d : ℝ := min ε (1/2)/2
  have hd : 0<d := half_pos (lt_min hε (by norm_num))
  have hdε : d<ε := by have := min_le_left ε (1/2:ℝ); dsimp [d]; linarith
  have hdhalf : d<1/2 := by have := min_le_right ε (1/2:ℝ); dsimp [d]; linarith
  have hpair : horizontalPair p rho.1 d<0 :=
    (hneg p hp d hd hdε).trans_lt (mul_neg_of_neg_of_pos (by linarith) (pow_pos hd _))
  have hs := shift_domain hr hd hdhalf
  by_cases h : (completedSplit p (rho.1+(d:ℂ))).re<0
  · refine ⟨rho.1+(d:ℂ),hs.1,?_,?_,h⟩
    · simpa using hT
    · simp only [Complex.add_re, Complex.ofReal_re, hr]
      linarith
  · refine ⟨rho.1-(d:ℂ),hs.2,?_,?_,?_⟩
    · simpa using hT
    · simp only [Complex.sub_re, Complex.ofReal_re, hr]
      linarith
    · dsimp [horizontalPair] at hpair
      linarith

/-- Blanket high-strip nonnegativity of the literal completed half is impossible. -/
theorem not_eventually_nonnegative_completedSplit {p : ℕ} (hp : 0<p) :
    ¬∃ T : ℝ, ∀ s : ℂ, s∈domain → T<s.im → 0 ≤ (completedSplit p s).re := by
  rintro ⟨T,hT⟩
  obtain ⟨s,hs,ht,_,hn⟩ := exists_high_negative_source hp T
  exact (not_le.mpr hn) (hT s hs ht)

end RHTower.DeletionHorizontalContact
end
