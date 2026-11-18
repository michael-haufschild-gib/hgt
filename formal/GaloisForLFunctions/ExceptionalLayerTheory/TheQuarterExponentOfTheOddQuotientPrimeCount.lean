import GaloisForLFunctions.ExceptionalLayerTheory.TheFiniteOddQuotientMeanOfProperPrimePowers

/-!
# A finite odd-quotient count characterizes RH at the quarter exponent

In the Mellin transform the integer squares and cubes remove the real
prime-power main terms. The dyadic multiplier is nonzero between one
quarter and one half. Holomorphy there forces the residues of the
distinct-prime-divisor moment to vanish, and halving excludes right zeros.
-/

noncomputable section
open Complex Set Filter Topology Finset ArithmeticFunction
open _root_.RHTower
namespace GaloisForLFunctions.ExceptionalLayerTheory

private abbrev coeff := properPowerLatticeWeight*alternatingDivisorCoeff
private abbrev transform (s : ℂ) :=
  alternatingDivisorFactor s*(properPowerLatticeMain s-firstPrimeDivisorMoment s)

private theorem factor_analytic (z : ℂ) : AnalyticAt ℂ alternatingDivisorFactor z := by
  have h : Differentiable ℂ (fun w : ℂ => (2:ℂ)^(-w)) := differentiable_neg.const_cpow (Or.inl (by norm_num))
  exact analyticAt_const.sub (analyticAt_const.mul (h.analyticAt z))

private theorem factor_nonzero {z : ℂ} (hz : z.re < 1) : alternatingDivisorFactor z ≠ 0 := by
  have he : (2:ℂ)^(1-z)=2*(2:ℂ)^(-z) := by
    rw [sub_eq_add_neg,Complex.cpow_add _ _ (by norm_num),Complex.cpow_one]
  apply sub_ne_zero.mpr
  rw [← he]
  intro h
  have hx : 1<‖((2:ℝ):ℂ)^(1-z)‖ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0:ℝ)<2),sub_re,one_re]
    exact Real.one_lt_rpow (by norm_num) (sub_pos.mpr hz)
  change 1<‖(2:ℂ)^(1-z)‖ at hx
  rw [← h,norm_one] at hx
  exact lt_irrefl _ hx

private theorem main_mero (z : ℂ) : MeromorphicAt properPowerLatticeMain z := by
  have hζ := meromorphicAt_riemannZeta_everywhere z
  have h (a : ℂ) : MeromorphicAt (fun w : ℂ => riemannZeta (a*w)) z :=
    (meromorphicAt_riemannZeta_everywhere (a*z)).comp_analyticAt (analyticAt_const.mul analyticAt_id)
  exact hζ.deriv.neg.sub (hζ.mul ((h 2).add (h 3)))

private theorem main_continuous {z : ℂ} (hi : z.im ≠ 0) : ContinuousAt properPowerLatticeMain z := by
  have hn (a : ℝ) (ha : a≠0) : (a:ℂ)*z ≠ 1 := by
    intro he
    exact (mul_ne_zero ha hi) (by simpa using congrArg Complex.im he)
  have h (a : ℝ) (ha : a≠0) : ContinuousAt (fun w : ℂ => riemannZeta ((a:ℂ)*w)) z :=
    (differentiableAt_riemannZeta (hn a ha)).continuousAt.comp
      (continuous_const.mul continuous_id).continuousAt
  have hζ := HTGeometry.analyticAt_riemannZeta (show z≠1 from fun e => hi (by rw [e,Complex.one_im]))
  exact hζ.deriv.continuousAt.neg.sub (hζ.continuousAt.mul ((h 2 (by norm_num)).add (h 3 (by norm_num))))

private theorem euler {s : ℂ} (hs : 3 < s.re) :
    triangularDirichletContinuation coeff s=transform s := by
  let f := fun n : ℕ => (coeff n:ℂ)
  have hf : LSeriesSummable f 2 := (oddQuotientPowerTotal_series (s := 2) (by norm_num)).1
  let M := ∑' n, ‖LSeries.term f 2 n‖
  have hcoef (n : ℕ) : |coeff (n+1)| ≤ M*((n:ℝ)+1)^(2:ℝ) := by
    have he : ‖LSeries.term f 2 (n+1)‖ ≤ M := hf.norm.le_tsum (n+1) (fun _ _ => norm_nonneg _)
    rw [LSeries.norm_term_eq,if_neg (Nat.succ_ne_zero n)] at he
    simp only [f,Complex.norm_real,Real.norm_eq_abs,show (2:ℂ).re=(2:ℝ) by norm_num,Nat.cast_succ] at he
    exact (div_le_iff₀ (by positivity : 0<((n:ℝ)+1)^(2:ℝ))).mp he
  have he := oddQuotientPowerTotal_series (s := s) (by linarith only [hs])
  rw [triangularDirichletContinuation_eq_series coeff hcoef (by linarith only [hs]) (by linarith only [hs])]
  apply Eq.trans _ he.2
  have ht := (hasSum_nat_add_iff' 1).mpr he.1.hasSum
  simp only [sum_range_one,LSeries.term_zero,sub_zero] at ht
  refine (tsum_congr (g := fun n => LSeries.term f s (n+1)) fun n => ?_).trans ht.tsum_eq
  rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n),Complex.cpow_neg,div_eq_mul_inv]
  simp [f]

/-- A bound on the finite mean forces the distinct-prime moment to have
zero residue at every nonreal point above its exponent and below one half. -/
theorem firstPrimeDivisorMoment_zero_residue_of_oddQuotientPowerTotal_bound {b K : ℝ} (hb : 1/4 < b) (hb' : b < 1/2) (hK : 0 ≤ K)
    (h : ∀ N : ℕ, 1≤N → |oddQuotientPowerTotal N| ≤ K*(N:ℝ)^(b+1))
    {z : ℂ} (hz : b < z.re) (h1 : z.re < 1/2) (hi : z.im ≠ 0) :
    Tendsto (fun w => (w-z)*firstPrimeDivisorMoment w) (𝓝[≠] z) (𝓝 0) := by
  let D := {w : ℂ | b < w.re}
  let G := triangularDirichletContinuation coeff
  have hop : IsOpen D := isOpen_lt continuous_const Complex.continuous_re
  have hprofile (N : ℕ) (hn : 1≤N) : |triangularPrimeProfile coeff (N:ℝ)⁻¹| ≤ K*(N:ℝ)^b := by
    have hh := h N hn
    have hp : (0:ℝ)<N := by exact_mod_cast hn
    rw [oddQuotientPowerTotal_eq_triangular,abs_mul,abs_of_pos hp,Real.rpow_add_one hp.ne'] at hh
    exact le_of_mul_le_mul_left (hh.trans_eq (by ring)) hp
  have hG : DifferentiableOn ℂ G D := fun _ h₀ =>
    (differentiableAt_triangularDirichletContinuation coeff hK (by linarith only [hb]) hprofile h₀).differentiableWithinAt
  let F : ℂ → ℂ := G-transform
  have hM : MeromorphicOn F D := by
    apply MeromorphicOn.sub (hG.analyticOnNhd hop).meromorphicOn
    exact fun w hw => (factor_analytic w).meromorphicAt.mul
      ((main_mero w).sub (firstPrimeDivisorMoment_meromorphicOn w (hb.trans hw)))
  have h4 : meromorphicOrderAt F (4:ℂ)=⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    have hnb : {w : ℂ | 3<w.re} ∈ 𝓝 (4:ℂ) := (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [nhdsWithin_le_nhds hnb] with w hw using sub_eq_zero.mpr (euler hw)
  have htop : meromorphicOrderAt F z=⊤ := by
    by_contra hne
    exact (hM.meromorphicOrderAt_ne_top_of_isPreconnected (convex_halfSpace_re_gt b).isPreconnected hz
      (show b < (4:ℂ).re by norm_num; linarith only [hb']) hne) h4
  have hg : G =ᶠ[𝓝[≠] z] transform := (meromorphicOrderAt_eq_top_iff.mp htop).mono fun _ e => sub_eq_zero.mp e
  have hf := factor_nonzero (show z.re<1 by linarith only [h1])
  have hlocal : firstPrimeDivisorMoment =ᶠ[𝓝[≠] z] fun w => properPowerLatticeMain w-G w/alternatingDivisorFactor w := by
    filter_upwards [hg,nhdsWithin_le_nhds ((factor_analytic z).continuousAt.eventually_ne hf)] with w hw hn
    change G w=alternatingDivisorFactor w*(properPowerLatticeMain w-firstPrimeDivisorMoment w) at hw
    rw [hw,mul_div_cancel_left₀ _ hn,sub_sub_cancel]
  have hcont := (main_continuous hi).sub ((hG.differentiableAt (hop.mem_nhds hz)).continuousAt.div
    (factor_analytic z).continuousAt hf)
  have hl : Tendsto (fun w : ℂ => w-z) (𝓝[≠] z) (𝓝 0) :=
    ((continuous_id.sub continuous_const).tendsto' z 0 (sub_self z)).mono_left nhdsWithin_le_nhds
  apply (tendsto_congr' (hlocal.mono fun w hw => congrArg ((w-z)*·) hw)).mpr
  simpa only [zero_mul] using hl.mul (hcont.tendsto.mono_left nhdsWithin_le_nhds)

/-- A single exponent below two sevenths for the finite count bounds the
real parts of all zeta zeros by twice that exponent. -/
theorem zero_free_strip_of_oddQuotientPowerTotal {b K : ℝ} (hb : 1/4 < b) (hb' : b < 2/7)
    (hK : 0 ≤ K) (h : ∀ N : ℕ, 1 ≤ N → |oddQuotientPowerTotal N| ≤ K*(N:ℝ)^(b+1))
    {s : ℂ} (hs : 2*b < s.re) : riemannZeta s ≠ 0 :=
  firstPrimeDivisorMoment_zero_free_of_vanishing_residues hb.le hb'
    (fun _ hz h1 hi => firstPrimeDivisorMoment_zero_residue_of_oddQuotientPowerTotal_bound hb (by linarith only [hb']) hK h hz h1 hi) hs

/-- All real main terms have been removed by counting ordinary squares
and cubes and taking an odd-quotient difference. -/
theorem riemannHypothesis_iff_oddQuotientPowerTotal_quarter :
    RiemannHypothesis ↔ ∀ b : ℝ, 1/4 < b → b < 1/2 →
      ∃ K : ℝ, 0≤K ∧ ∀ N : ℕ, 1≤N → |oddQuotientPowerTotal N| ≤ K*(N:ℝ)^(b+1) := by
  constructor
  · exact fun h _ hb hb' => oddQuotientPowerTotal_quarter_of_rh h hb hb'
  · intro h
    apply riemannHypothesis_of_firstPrimeDivisorMoment_zero_residues
    intro z hz hz' hi
    obtain ⟨b,hb,hbz⟩ := exists_between hz
    obtain ⟨K,hK,hN⟩ := h b hb (hbz.trans hz')
    exact firstPrimeDivisorMoment_zero_residue_of_oddQuotientPowerTotal_bound hb (hbz.trans hz') hK hN hbz hz' hi

end GaloisForLFunctions.ExceptionalLayerTheory
