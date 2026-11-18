import GaloisForLFunctions.CountingHolography.Sections.OneMultiplicityPerSquareConductor
import GaloisForLFunctions.CountingHolography.Sections.UnitMultiplicityOnThePoleHyperplane

/-! # Sparse square conductors detect every zero strip

A power saving in the conductor gaps gives a strict saving over the
actual zero width in the changes of both long traces. The all-conductor
criterion absorbs this error even when no zero attains the extremal width.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Filter Finset Topology SurfaceOfSpecZ SquareRootThreshold Zeta23 ArithmeticScatteringHolography

private def degree (n : ℕ) := integerProbe _ (successorSquareTriple n)
private def X (n : ℕ) := (n:ℝ)+1
private def high (z : ℝ) := 2*z+1

private theorem degree_increment : ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ {d n : ℕ}, 0 < d → d ≤ n →
    |degree n-degree d| ≤ D+C*(Real.log n-Real.log d)*Real.exp ((2*zetaZeroWidth)*Real.log n) := by
  obtain ⟨L,hL,hinc⟩ := realSplineTrace_increment
  obtain ⟨B,hB,hrem⟩ := successorSquare_degree_long_lags
  let w := zetaZeroWidth
  let K := Real.exp ((2*w)*Real.log 3)
  refine ⟨(8+4*K)*L,2*B,by dsimp only [K]; positivity,by positivity,fun {d n} hd hdn => ?_⟩
  have hd₁ : 1 ≤ (d:ℝ) := by exact_mod_cast hd
  have hdn' : (d:ℝ) ≤ n := by exact_mod_cast hdn
  have hn₁ := hd₁.trans hdn'
  have hd₀ := zero_lt_one.trans_le hd₁
  have hn₀ := hd₀.trans_le hdn'
  have hl := Real.log_le_log hd₀ hdn'
  have hdiff := sub_nonneg.mpr hl
  have ha := hinc (2*Real.log d) (2*Real.log n) (mul_nonneg two_pos.le (Real.log_nonneg hd₁))
    (mul_le_mul_of_nonneg_left hl two_pos.le)
  have hhd : 1 ≤ high d := by dsimp only [high]; linarith
  have hh : high d ≤ high n := by dsimp only [high]; linarith only [hdn']
  have hd' := zero_lt_one.trans_le hhd
  have hn' := hd'.trans_le hh
  have hlh := Real.log_le_log hd' hh
  have hb := hinc (2*Real.log (high d)) (2*Real.log (high n)) (mul_nonneg two_pos.le (Real.log_nonneg hhd))
    (mul_le_mul_of_nonneg_left hlh two_pos.le)
  have hlog : Real.log (high n)-Real.log (high d) ≤ Real.log n-Real.log d := by
    rw [← Real.log_div hn'.ne' hd'.ne',← Real.log_div hn₀.ne' hd₀.ne']
    apply Real.log_le_log (div_pos hn' hd') ((div_le_div_iff₀ hd' hd₀).mpr ?_)
    dsimp only [high]
    linarith only [hdn']
  have hup : Real.log (high n) ≤ Real.log 3+Real.log n := by
    rw [← Real.log_mul (by norm_num : (3:ℝ)≠0) hn₀.ne']
    exact Real.log_le_log hn' (by dsimp only [high]; linarith only [hn₁])
  have he : Real.exp (w*(2*Real.log (high n))) ≤ K*Real.exp ((2*w)*Real.log n) := by
    dsimp only [K]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith only [mul_le_mul_of_nonneg_left hup (mul_nonneg two_pos.le zetaZeroWidth_nonneg)]
  have he₁ := mul_le_mul (mul_le_mul_of_nonneg_left
    (show 2*Real.log (high n)-2*Real.log (high d) ≤ 2*(Real.log n-Real.log d) by linarith only [hlog]) hL)
    he (Real.exp_pos _).le (by positivity : 0 ≤ L*(2*(Real.log n-Real.log d)))
  have hdrem := abs_le.mp (hrem d hd)
  have hnrem := abs_le.mp (hrem n (hd.trans_le hdn))
  change -B ≤ degree d-(4*realSplineTrace (2*Real.log d)-2*realSplineTrace (2*Real.log ((2*d+1:ℕ):ℝ))) ∧ _ at hdrem
  change -B ≤ degree n-(4*realSplineTrace (2*Real.log n)-2*realSplineTrace (2*Real.log ((2*n+1:ℕ):ℝ))) ∧ _ at hnrem
  push_cast at hdrem hnrem
  change |realSplineTrace (2*Real.log (high n))-realSplineTrace (2*Real.log (high d))| ≤ _ at hb
  have ha' := abs_le.mp ha
  have hb' := abs_le.mp (hb.trans he₁)
  dsimp only [high] at hb'
  rw [show w*(2*Real.log n)=(2*w)*Real.log n by ring] at ha'
  rw [abs_le]
  constructor <;> linarith only [hdrem.1,hdrem.2,hnrem.1,hnrem.2,ha'.1,ha'.2,hb'.1,hb'.2]

private theorem extend_lower {r A : ℝ} (hr : 0 ≤ r)
    (h : ∀ᶠ n : ℕ in atTop, -(A*(X n)^r) ≤ degree n) :
    ∃ B : ℝ, ∀ n : ℕ, 0 < n → -(B*(X n)^r) ≤ degree n := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp h
  let F := ∑ j ∈ range N, |degree j|
  have hF : 0 ≤ F := sum_nonneg fun j _ => abs_nonneg _
  refine ⟨max A F,fun n _ => ?_⟩
  have hX : 1 ≤ X n := by dsimp only [X]; linarith only [Nat.cast_nonneg (α := ℝ) n]
  have hp := Real.one_le_rpow hX hr
  by_cases hn : N ≤ n
  · exact (neg_le_neg (mul_le_mul_of_nonneg_right (le_max_left A F) (zero_le_one.trans hp))).trans (hN n hn)
  · have hsmall : |degree n| ≤ F := single_le_sum (s := range N) (f := fun j => |degree j|)
      (fun j _ => abs_nonneg _) (mem_range.mpr (lt_of_not_ge hn))
    have hb := (le_max_right A F).trans (le_mul_of_one_le_right (hF.trans (le_max_right A F)) hp)
    exact (neg_le_neg (hsmall.trans hb)).trans (neg_abs_le _)

/-- A single sampled lower bound per power gap detects the full width.
Both the gap exponent and its implicit constant may depend on the sample set. -/
theorem zetaZeroWidth_le_iff_sparse_square_degrees {θ s : ℝ} {E : Set ℕ}
    (hθ : θ < 1) (hE : PowGaps θ E) (hs : 0 ≤ s) (hs' : s < 1/2) :
    zetaZeroWidth ≤ s ↔ ∃ A : ℝ, ∀ n ∈ E,
      -(A*((n:ℝ)+1)^(2*s)) ≤ integerProbe _ (successorSquareTriple n) := by
  constructor
  · intro hw
    obtain ⟨A,hA⟩ := (zetaZeroWidth_le_iff_successorSquareTriple hs hs').mp hw
    exact ⟨A,fun n hn => hA n (hE.1 n hn)⟩
  rintro ⟨A,hA⟩
  by_contra! hsw
  let w := zetaZeroWidth
  let t := max s ((2*w+θ-1)/2)
  have hst : s ≤ t := le_max_left _ _
  have ht := hs.trans hst
  have htw : t < w := max_lt hsw (by linarith only [hθ])
  have ht' : t < 1/2 := htw.trans_le zetaZeroWidth_le_half
  obtain ⟨C,D,hC,hD,hinc⟩ := degree_increment
  obtain ⟨M,T,hM,_,hgap⟩ := exists_log_degree_near hθ hE
  have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have htail : ∀ᶠ n : ℕ in atTop, -((|A|+D+2*C*M)*(X n)^(2*t)) ≤ degree n := by
    filter_upwards [hlog.eventually_ge_atTop T,eventually_ge_atTop 1] with n hnT hn
    have hn₁ : 1 ≤ (n:ℝ) := by exact_mod_cast hn
    have hn₀ := zero_lt_one.trans_le hn₁
    have hlu := Real.log_nonneg hn₁
    obtain ⟨d,hd,hdn,hv,hvu,hg⟩ := hgap (Real.log n) hnT
    rw [Real.exp_log hn₀] at hdn
    have he := abs_le.mp (hinc (hE.1 d hd) (by exact_mod_cast hdn : d ≤ n))
    have hE₁ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg hC)
      (Real.exp_pos ((2*w)*Real.log n)).le
    have hsum : C*(2*M*Real.exp ((θ-1)*Real.log n))*Real.exp ((2*w)*Real.log n)=
        (2*C*M)*Real.exp ((2*w+θ-1)*Real.log n) := by
      rw [show (2*w+θ-1)*Real.log n=(θ-1)*Real.log n+(2*w)*Real.log n by ring,Real.exp_add]
      ring
    rw [hsum] at hE₁
    have hX : (n:ℝ) ≤ X n := by dsimp only [X]; linarith
    have hX₁ := hn₁.trans hX
    have hpow := Real.one_le_rpow hX₁ (mul_nonneg two_pos.le ht)
    have hgrowth : Real.exp ((2*w+θ-1)*Real.log n) ≤ (X n)^(2*t) := by
      calc _ ≤ Real.exp ((2*t)*Real.log n) := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
                (by linarith only [show (2*w+θ-1)/2 ≤ t from le_max_right _ _]) hlu)
        _ = (n:ℝ)^(2*t) := by rw [Real.rpow_def_of_pos hn₀,mul_comm]
        _ ≤ _ := Real.rpow_le_rpow hn₀.le hX (mul_nonneg two_pos.le ht)
    have hdX : 0 < X d := by dsimp only [X]; positivity
    have hA₁ := mul_le_mul (le_abs_self A)
      ((Real.rpow_le_rpow hdX.le (add_le_add_right hdn 1) (mul_nonneg two_pos.le hs)).trans
        (Real.rpow_le_rpow_of_exponent_le hX₁ (mul_le_mul_of_nonneg_left hst two_pos.le)))
      (Real.rpow_nonneg hdX.le _) (abs_nonneg A)
    have hdlo : -(A*(X d)^(2*s)) ≤ degree d := hA d hd
    linarith only [he.1,hE₁,mul_le_mul_of_nonneg_left hgrowth (by positivity : 0 ≤ 2*C*M),
      le_mul_of_one_le_right hD hpow,hA₁,hdlo]
  obtain ⟨B,hB⟩ := extend_lower (mul_nonneg two_pos.le ht) htail
  exact htw.not_ge ((zetaZeroWidth_le_iff_successorSquareTriple ht ht').mpr ⟨B,hB⟩)

/-- Sparse diagonal logarithmic allowances give a strip of the same width. -/
theorem zetaZeroWidth_le_of_sparse_square_logs {θ s A : ℝ} {E : Set ℕ}
    (hθ : θ < 1) (hE : PowGaps θ E) (hs : 0 ≤ s) (hs' : s < 1/2) (hA : 0 ≤ A)
    (hfit : ∀ n ∈ E, Real.log (ordinaryPrimeGenerator (n • successorSquareTriple n):ℝ) ≤
      A*(n:ℝ)^(2+2*s)) : zetaZeroWidth ≤ s := by
  obtain ⟨D,hD,herr⟩ := successorSquare_degree_window_error
  apply (zetaZeroWidth_le_iff_sparse_square_degrees hθ hE hs hs').mpr
  refine ⟨A+4*D,fun n hn => ?_⟩
  have hn' := hE.1 n hn
  have hn₁ : (1:ℝ) ≤ n := by exact_mod_cast hn'
  have hn₀ := zero_lt_one.trans_le hn₁
  have hs₀ := mul_nonneg two_pos.le hs
  have hlog := hfit n hn
  rw [Real.rpow_add hn₀,Real.rpow_two] at hlog
  have hd := (abs_le.mp (herr hn' hn' (by linarith only [hn₁]))).1
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ (n:ℝ)+1)
    (by linarith only [hn₁] : (n:ℝ)+1 ≤ 2*n) 2
  have hp := Real.rpow_le_rpow hn₀.le (by linarith : (n:ℝ) ≤ n+1) hs₀
  have hterm := mul_le_mul_of_nonneg_left hp (mul_nonneg hA (sq_nonneg (n:ℝ)))
  have hlarge := (Real.one_le_rpow (by linarith only [hn₁] : 1 ≤ (n:ℝ)+1) hs₀)
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hn₀)).mp
  linarith only [hd,hlog,hterm,mul_le_mul_of_nonneg_left hsq hD,
    le_mul_of_one_le_right (mul_nonneg hD (sq_nonneg (n:ℝ))) hlarge]

/-- The actual comparison of two positive rationals detects RH on any
conductor set with a power saving in its gaps. -/
theorem riemannHypothesis_iff_sparse_square_power {θ : ℝ} {E : Set ℕ}
    (hθ : θ < 1) (hE : PowGaps θ E) :
    RiemannHypothesis ↔ ∃ B : ℕ, 0 < B ∧ ∀ n ∈ E,
      ordinaryPrimeGenerator (n • successorSquareTriple n) ≤ (B:ℚ)^(n^2) := by
  constructor
  · intro hRH
    obtain ⟨B,hB,h⟩ := riemannHypothesis_iff_diagonal_successorSquare_power.mp hRH
    exact ⟨B,hB,fun n hn => h n (hE.1 n hn)⟩
  rintro ⟨B,hB,hfit⟩
  apply riemannHypothesis_iff_zetaZeroWidth_eq_zero.mpr
  apply le_antisymm _ zetaZeroWidth_nonneg
  have hlogB : 0 ≤ Real.log (B:ℝ) := Real.log_natCast_nonneg B
  apply zetaZeroWidth_le_of_sparse_square_logs hθ hE (s := 0) le_rfl (by norm_num) hlogB
  intro n hn
  have hlog := (generator_le_power_iff (n • successorSquareTriple n) hB 1 n).mp
    (by simpa only [one_mul] using hfit n hn)
  simpa only [Nat.cast_one,one_pow,mul_one,mul_zero,add_zero,Real.rpow_two] using hlog

/-- One common exponential allowance at the k-th-power conductors suffices,
even for arbitrarily large fixed k. -/
theorem riemannHypothesis_iff_perfect_power_square_generators {k : ℕ} (hk : 1 ≤ k) :
    RiemannHypothesis ↔ ∃ B : ℕ, 0 < B ∧ ∀ j : ℕ, 0 < j →
      ordinaryPrimeGenerator ((j^k) • successorSquareTriple (j^k)) ≤ (B:ℚ)^((j^k)^2) := by
  rw [riemannHypothesis_iff_sparse_square_power (one_sub_inv_lt_one hk) (powGaps_kthPowers hk)]
  constructor
  · rintro ⟨B,hB,h⟩
    exact ⟨B,hB,fun j hj => h (j^k) ⟨j,hj,rfl⟩⟩
  · rintro ⟨B,hB,h⟩
    refine ⟨B,hB,?_⟩
    rintro _ ⟨j,hj,rfl⟩
    exact h j hj

/-- Off the line, every exponential allowance fails simultaneously at
every conductor in arbitrarily late intervals of any fixed sublinear power length. -/
theorem square_power_fails_on_long_intervals (hRH : ¬RiemannHypothesis)
    {θ M : ℝ} (hθ : θ < 1) (hM : 0 ≤ M) {B : ℕ} (hB : 0 < B) (X : ℝ) :
    ∃ x ≥ X, ∀ n : ℕ, 0 < n → (n:ℝ) ≤ x → x-n ≤ M*x^θ →
      (B:ℚ)^(n^2) < ordinaryPrimeGenerator (n • successorSquareTriple n) := by
  let E := {n : ℕ | 0 < n ∧ ordinaryPrimeGenerator (n • successorSquareTriple n) ≤ (B:ℚ)^(n^2)}
  by_contra! h
  have hg : PowGaps θ E := by
    refine ⟨fun _ hn => hn.1,M,X,hM,fun x hx => ?_⟩
    obtain ⟨n,hn,hnx,hgap,hfit⟩ := h x hx
    exact ⟨n,⟨hn,hfit⟩,hnx,hgap⟩
  exact hRH ((riemannHypothesis_iff_sparse_square_power hθ hg).mpr ⟨B,hB,fun _ hn => hn.2⟩)

end GaloisForLFunctions.CountingHolography.Sections
