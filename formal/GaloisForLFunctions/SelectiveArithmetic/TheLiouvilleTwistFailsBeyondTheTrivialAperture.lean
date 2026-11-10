import GaloisForLFunctions.SelectiveArithmetic.ThePolarPacketsOfAWindow

/-!
# The Liouville twist fails beyond the trivial aperture

Below the aperture `log log q − o(1)` the form of every dominated system with conductor `q` is
positive (`exists_systemForm_margin`). Three dominated systems fail immediately beyond it,
whatever the conductor:

* the **Liouville twist** `w(p^k) = (−1)^k log p`: the contacts of a completely multiplicative
  function with values `±1`, the sizes of a real character, no conductor;
* `w = −Λ`, the contacts of `1/ζ`, which has a zero at `s = 1`;
* `w = Λ`, the contacts of `ζ`, without its pole plane.

**Theorem** (`exists_systemForm_polar_neg`, `exists_not_feasible`). For every `η > 0` and every
conductor with `log q` large, at every aperture `a ≥ log log q + η` the form of the Liouville
twist and of `−Λ` is negative on the odd polar packet `sinh(u/2) χ(u)`, and the form of `Λ` is
negative on the even polar packet `cosh(u/2) χ(u)`.

**Theorem** (`tendsto_trivialAperture_sub_log`). The trivial aperture of a conductor, the supremum
of the apertures at which the whole dominated box is feasible, is `log log q + o(1)`.

So the ladder of the conductor has no gap: the sizes of the contacts prove the sign up to
`log log q − o(1)` and nothing beyond, and a statement at aperture `log log q + C`, `C > 0`,
separates a character from the Liouville twist.

**Mechanism.** The form of a system on a smooth packet is at most
`(5 + log q) ∫ f² + ∫ f'² −` contact form (`systemForm_le_of_packet`), since the archimedean
symbol is at most `5 + τ²`. The even polar packet has mass `≤ a + sinh a` and its contact form
with `Λ` is at least half the Riesz mean `Σ_{n ≤ Y} Λ(n) log(Y/n)`, `Y = e^{2a − 2δ}`, which is
`(1 − η')Y` by the prime number theorem (corpus). The correlations of the two polar packets add up
to the polar kernel, so the contact form of the odd packet with `Λ` is at most
`4a e^{a} Σ Λ(n)/n` minus that of the even one. The Liouville twist is `−Λ` plus twice the
contacts at the squares, which cost `Σ_m Λ(m)/m` times the mass.
-/

open Finset Filter Topology MeasureTheory
open Zeta23
open scoped ArithmeticFunction.vonMangoldt Real

noncomputable section

namespace GaloisForLFunctions.SelectiveArithmetic

open AbsoluteGeometryOfSpecZ BiScaleUncertainty

/-! ### The contact form on a real packet -/

theorem contactForm_packet (w : ℕ → ℝ) (f : ℝ → ℝ) (N : ℕ) :
    contactForm w (fun u => (f u : ℂ)) N =
      ∑ n ∈ Finset.Icc 2 N, w n / Real.sqrt n * (2 * packetAutocorr f (Real.log n)) := by
  unfold contactForm
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [weilTest_packet, weilTest_packet, packetAutocorr_neg, ← Complex.ofReal_add,
    Complex.ofReal_re]
  ring

theorem contactForm_neg (w : ℕ → ℝ) (F : ℝ → ℂ) (N : ℕ) :
    contactForm (fun n => -w n) F N = -contactForm w F N := by
  unfold contactForm
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun n _ => by ring

/-! ### An upper bound of the form of a system on a smooth packet -/

/-- The archimedean symbol is at most `5 + τ²`. -/
theorem archimedeanWeilSymbol_le_five_add_sq (τ : ℝ) :
    _root_.RHTower.archimedeanWeilSymbol (τ / (2 * π)) ≤ 5 + τ ^ 2 := by
  have h := _root_.RHTower.archimedeanWeilSymbol_le_log_add τ
  have h1 : Real.log (1 + |τ|) ≤ |τ| := by
    have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + |τ|)
    linarith
  have h2 : |τ| ≤ 1 + τ ^ 2 := by
    nlinarith [sq_nonneg (|τ| - 1), sq_abs τ, abs_nonneg τ]
  linarith

/-- **The archimedean energy of a smooth packet** is at most `5 ∫ f² + ∫ f'²`. -/
theorem integral_arch_le {a : ℝ} {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    (h0 : ∀ u, a ≤ |u| → f u = 0) :
    1 / (2 * π) * ∫ τ : ℝ, ‖paperFT (fun u => (f u : ℂ)) τ‖ ^ 2 *
        _root_.RHTower.archimedeanWeilSymbol (τ / (2 * π)) ≤
      5 * (∫ u, f u ^ 2) + ∫ u, deriv f u ^ 2 := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have hF : ContDiff ℝ 2 fun u => (f u : ℂ) := contDiff_ofReal_packet hf2
  have hFs : tsupport (fun u => (f u : ℂ)) ⊆ Set.Icc (-a) a :=
    tsupport_ofReal_subset_of_eq_zero h0
  have hFc : HasCompactSupport fun u => (f u : ℂ) :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) hFs
  -- the derivative as a test
  have hd2 : ContDiff ℝ 2 (deriv f) := by
    have h : ContDiff ℝ (2 + 1) f := by
      have e : ((2 : WithTop ℕ∞) + 1) = 3 := by norm_num
      rw [e]
      exact hf
    exact (contDiff_succ_iff_deriv.mp h).2.2
  have hG : ContDiff ℝ 2 fun u => ((deriv f u : ℝ) : ℂ) := contDiff_ofReal_packet hd2
  have hderiv : deriv (fun u => (f u : ℂ)) = fun u => ((deriv f u : ℝ) : ℂ) := by
    funext u
    exact ((hf2.differentiable (by norm_num) u).hasDerivAt.ofReal_comp).deriv
  have hGs : tsupport (fun u => ((deriv f u : ℝ) : ℂ)) ⊆ Set.Icc (-a) a := by
    rw [← hderiv]
    exact (tsupport_deriv_subset (f := fun u => (f u : ℂ))).trans hFs
  have hnorm : ∀ τ : ℝ, ‖paperFT (fun u => ((deriv f u : ℝ) : ℂ)) τ‖ ^ 2 =
      τ ^ 2 * ‖paperFT (fun u => (f u : ℂ)) τ‖ ^ 2 := fun τ => by
    have h := _root_.RHTower.EvenSector.paperFT_deriv_of_compact (hF.of_le (by norm_num)) hFc
      (τ : ℂ)
    rw [hderiv] at h
    rw [h, norm_mul, mul_pow, norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
  have hI := _root_.RHTower.integrable_normSq_paperFT hF hFs
  have hI' := _root_.RHTower.integrable_normSq_paperFT hG hGs
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hmono : ∫ τ : ℝ, ‖paperFT (fun u => (f u : ℂ)) τ‖ ^ 2 *
        _root_.RHTower.archimedeanWeilSymbol (τ / (2 * π)) ≤
      ∫ τ : ℝ, (5 * ‖paperFT (fun u => (f u : ℂ)) τ‖ ^ 2 +
        ‖paperFT (fun u => ((deriv f u : ℝ) : ℂ)) τ‖ ^ 2) := by
    refine integral_mono (_root_.RHTower.integrable_normSq_paperFT_mul_arch hF hFs)
      ((hI.const_mul 5).add hI') fun τ => ?_
    show ‖paperFT (fun u => (f u : ℂ)) τ‖ ^ 2 *
        _root_.RHTower.archimedeanWeilSymbol (τ / (2 * π)) ≤
      5 * ‖paperFT (fun u => (f u : ℂ)) τ‖ ^ 2 +
        ‖paperFT (fun u => ((deriv f u : ℝ) : ℂ)) τ‖ ^ 2
    rw [hnorm]
    nlinarith [mul_le_mul_of_nonneg_left (archimedeanWeilSymbol_le_five_add_sq τ)
      (sq_nonneg ‖paperFT (fun u => (f u : ℂ)) τ‖)]
  rw [integral_add (hI.const_mul 5) hI', integral_const_mul,
    _root_.RHTower.integral_norm_paperFT_sq hF hFs,
    _root_.RHTower.integral_norm_paperFT_sq hG hGs, integral_norm_ofReal_sq,
    integral_norm_ofReal_sq] at hmono
  have h1 := mul_le_mul_of_nonneg_left hmono (by positivity : (0 : ℝ) ≤ 1 / (2 * π))
  have e : 1 / (2 * π) * (5 * (2 * π * ∫ u, f u ^ 2) + 2 * π * ∫ u, deriv f u ^ 2) =
      5 * (∫ u, f u ^ 2) + ∫ u, deriv f u ^ 2 := by
    field_simp
  rwa [e] at h1

/-- **The form of a system on a smooth packet** is at most
`(5 + log q) ∫ f² + ∫ f'²` minus its contact form. -/
theorem systemForm_le_of_packet {a : ℝ} {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    (h0 : ∀ u, a ≤ |u| → f u = 0) (w : ℕ → ℝ) (q : ℝ) :
    systemForm w q a (fun u => (f u : ℂ)) ≤
      (5 + Real.log q) * (∫ u, f u ^ 2) + (∫ u, deriv f u ^ 2) -
        contactForm w (fun u => (f u : ℂ)) ⌊Real.exp (2 * a)⌋₊ := by
  have hF : ContDiff ℝ 2 fun u => (f u : ℂ) := contDiff_ofReal_packet (hf.of_le (by norm_num))
  rw [systemForm_eq hF (tsupport_ofReal_subset_of_eq_zero h0), integral_norm_ofReal_sq]
  have h := integral_arch_le hf h0
  have e : (5 + Real.log q) * (∫ u, f u ^ 2) =
      5 * (∫ u, f u ^ 2) + Real.log q * ∫ u, f u ^ 2 := by ring
  linarith

/-! ### The Liouville twist -/

open Classical in
/-- The Liouville twist of the contacts: `Λ(n)` at the squares and `−Λ(n)` elsewhere, that is
`(−1)^k log p` at `n = p^k`. -/
def liouvilleWeight (n : ℕ) : ℝ := if IsSquare n then Λ n else -Λ n

theorem dominated_liouvilleWeight : Dominated liouvilleWeight := fun n => by
  unfold liouvilleWeight
  split_ifs
  · exact (abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg).le
  · rw [abs_neg]
    exact (abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg).le

/-- A power of a prime is a square exactly when its exponent is even. -/
theorem isSquare_prime_pow_iff {p k : ℕ} (hp : p.Prime) : IsSquare (p ^ k) ↔ Even k := by
  constructor
  · rintro ⟨r, hr⟩
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hr
      exact (pow_ne_zero k hp.ne_zero) hr
    have h := congrArg (fun n => n.factorization p) hr
    simp only [hp.factorization_pow, Nat.factorization_mul hr0 hr0, Finsupp.single_eq_same,
      Finsupp.coe_add, Pi.add_apply] at h
    exact ⟨_, h⟩
  · rintro ⟨j, rfl⟩
    exact ⟨p ^ j, pow_add p j j⟩

/-- **The Liouville twist at a prime power**: `(−1)^k log p`. -/
theorem liouvilleWeight_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    liouvilleWeight (p ^ k) = (-1) ^ k * Real.log p := by
  have hΛ : (Λ (p ^ k) : ℝ) = Real.log p := by
    rw [ArithmeticFunction.vonMangoldt_apply_pow hk, ArithmeticFunction.vonMangoldt_apply_prime hp]
  unfold liouvilleWeight
  by_cases he : Even k
  · rw [if_pos ((isSquare_prime_pow_iff hp).mpr he), hΛ, he.neg_one_pow, one_mul]
  · rw [if_neg (fun h => he ((isSquare_prime_pow_iff hp).mp h)), hΛ,
      (Nat.not_even_iff_odd.mp he).neg_one_pow]
    ring

open Classical in
/-- The contacts at the squares. -/
def squareWeight (n : ℕ) : ℝ := if IsSquare n then Λ n else 0

theorem squareWeight_nonneg (n : ℕ) : 0 ≤ squareWeight n := by
  unfold squareWeight
  split_ifs
  · exact ArithmeticFunction.vonMangoldt_nonneg
  · exact le_rfl

/-- The Liouville twist is `−Λ` plus twice the contacts at the squares. -/
theorem contactForm_liouvilleWeight (F : ℝ → ℂ) (N : ℕ) :
    contactForm liouvilleWeight F N =
      -contactForm (fun n => Λ n) F N + 2 * contactForm squareWeight F N := by
  unfold contactForm
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  unfold liouvilleWeight squareWeight
  split_ifs <;> ring

/-- The squares below `N` carry at most the mass `Σ_{m ≤ N} Λ(m)/m`. -/
theorem sum_squareWeight_div_sqrt_le (N : ℕ) :
    ∑ n ∈ Finset.Icc 2 N, squareWeight n / Real.sqrt n ≤
      ∑ m ∈ Finset.Icc 1 N, (Λ m : ℝ) / m := by
  classical
  have hterm : ∀ n : ℕ, 0 ≤ (Λ n : ℝ) / Real.sqrt n := fun n =>
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  have h1 : ∑ n ∈ Finset.Icc 2 N, squareWeight n / Real.sqrt n =
      ∑ n ∈ (Finset.Icc 2 N).filter IsSquare, (Λ n : ℝ) / Real.sqrt n := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    unfold squareWeight
    split_ifs
    · rfl
    · rw [zero_div]
  have hsub : (Finset.Icc 2 N).filter IsSquare ⊆
      (Finset.Icc 1 N).image fun m : ℕ => m * m := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn2, hnN⟩, r, rfl⟩ := hn
    have hr1 : 1 ≤ r := by
      rcases Nat.eq_zero_or_pos r with h | h
      · subst h
        omega
      · exact h
    exact Finset.mem_image.mpr ⟨r, Finset.mem_Icc.mpr ⟨hr1, (Nat.le_mul_self r).trans hnN⟩, rfl⟩
  have hinj : Set.InjOn (fun m : ℕ => m * m) ((Finset.Icc 1 N : Finset ℕ) : Set ℕ) :=
    fun x _ y _ h => Nat.mul_self_inj.mp h
  rw [h1]
  calc ∑ n ∈ (Finset.Icc 2 N).filter IsSquare, (Λ n : ℝ) / Real.sqrt n
      ≤ ∑ n ∈ (Finset.Icc 1 N).image fun m : ℕ => m * m, (Λ n : ℝ) / Real.sqrt n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => hterm n
    _ = ∑ m ∈ Finset.Icc 1 N, (Λ (m * m) : ℝ) / Real.sqrt ((m * m : ℕ) : ℝ) :=
        Finset.sum_image hinj
    _ = ∑ m ∈ Finset.Icc 1 N, (Λ m : ℝ) / m := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [← sq, ArithmeticFunction.vonMangoldt_apply_pow two_ne_zero, sq, Nat.cast_mul,
          Real.sqrt_mul_self (Nat.cast_nonneg m)]

/-- The contacts at the squares cost `2 Σ_{m ≤ N} Λ(m)/m` times the mass of a packet. -/
theorem abs_contactForm_squareWeight_le {f : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (N : ℕ) :
    |contactForm squareWeight (fun u => (f u : ℂ)) N| ≤
      2 * (∑ m ∈ Finset.Icc 1 N, (Λ m : ℝ) / m) * ∫ u, f u ^ 2 := by
  have hmass : 0 ≤ ∫ u, f u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  rw [contactForm_packet]
  calc |∑ n ∈ Finset.Icc 2 N, squareWeight n / Real.sqrt n *
          (2 * packetAutocorr f (Real.log n))|
      ≤ ∑ n ∈ Finset.Icc 2 N, squareWeight n / Real.sqrt n * (2 * ∫ u, f u ^ 2) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
        have hw : 0 ≤ squareWeight n / Real.sqrt n :=
          div_nonneg (squareWeight_nonneg n) (Real.sqrt_nonneg _)
        rw [abs_mul, abs_of_nonneg hw, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (abs_packetAutocorr_le hf hfc _) (by norm_num)) hw
    _ = (∑ n ∈ Finset.Icc 2 N, squareWeight n / Real.sqrt n) * (2 * ∫ u, f u ^ 2) :=
        (Finset.sum_mul _ _ _).symm
    _ ≤ (∑ m ∈ Finset.Icc 1 N, (Λ m : ℝ) / m) * (2 * ∫ u, f u ^ 2) :=
        mul_le_mul_of_nonneg_right (sum_squareWeight_div_sqrt_le N) (by positivity)
    _ = 2 * (∑ m ∈ Finset.Icc 1 N, (Λ m : ℝ) / m) * ∫ u, f u ^ 2 := by ring

/-! ### The contact forms of the polar packets -/

/-- Mertens' bound on the window: `Σ_{n ≤ e^{2a}} Λ(n)/n ≤ (2 + 2a)²`. -/
theorem sum_vonMangoldt_div_window_le {a : ℝ} (ha : 0 ≤ a) :
    ∑ n ∈ Finset.Icc 1 ⌊Real.exp (2 * a)⌋₊, (Λ n : ℝ) / n ≤ (2 + 2 * a) ^ 2 := by
  have h := sum_vonMangoldt_div_le_of_lt_exp (S := Finset.Icc 1 ⌊Real.exp (2 * a)⌋₊)
    (τ := 2 * a + 1) (by linarith) fun n hn => by
      rw [Finset.mem_Icc] at hn
      refine ⟨hn.1, ?_⟩
      calc (n : ℝ) ≤ ⌊Real.exp (2 * a)⌋₊ := Nat.cast_le.mpr hn.2
        _ ≤ Real.exp (2 * a) := Nat.floor_le (Real.exp_pos _).le
        _ < Real.exp (2 * a + 1) := Real.exp_lt_exp.mpr (by linarith)
  calc _ ≤ (1 + (2 * a + 1)) ^ 2 := h
    _ = (2 + 2 * a) ^ 2 := by ring

/-- **The even polar packet sees the Riesz mean of the primes.** Its contact form with `Λ` is at
least `½ Σ_{n ≤ Y} Λ(n) log(Y/n)`, `Y = e^{2a − 2δ}`. -/
theorem contactForm_evenPolar_ge {a δ : ℝ} (hδ : 0 < δ) :
    1 / 2 * ∑ n ∈ Finset.Icc 1 ⌊Real.exp (2 * a - 2 * δ)⌋₊,
        (Λ n : ℝ) * Real.log (Real.exp (2 * a - 2 * δ) / n) ≤
      contactForm (fun n => Λ n) (fun u => (evenPolar a δ u : ℂ)) ⌊Real.exp (2 * a)⌋₊ := by
  classical
  set Y := Real.exp (2 * a - 2 * δ) with hY
  set N := ⌊Real.exp (2 * a)⌋₊ with hN
  have hYN : ⌊Y⌋₊ ≤ N :=
    Nat.floor_le_floor (Real.exp_le_exp.mpr (by linarith))
  rw [contactForm_packet]
  have hT : ∀ n : ℕ, 0 ≤ (Λ n : ℝ) / Real.sqrt n *
      (2 * packetAutocorr (evenPolar a δ) (Real.log n)) := fun n =>
    mul_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
      (mul_nonneg zero_le_two (packetAutocorr_evenPolar_nonneg a δ _))
  -- drop `n = 1`, where `Λ = 0`
  have h1 : ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, (Λ n : ℝ) * Real.log (Y / n) =
      ∑ n ∈ Finset.Icc 2 ⌊Y⌋₊, (Λ n : ℝ) * Real.log (Y / n) := by
    refine (Finset.sum_subset (fun n hn => ?_) fun n hn hn2 => ?_).symm
    · rw [Finset.mem_Icc] at hn ⊢
      omega
    · have : n = 1 := by
        rw [Finset.mem_Icc] at hn hn2
        omega
      subst this
      simp
  rw [h1, Finset.mul_sum]
  calc ∑ n ∈ Finset.Icc 2 ⌊Y⌋₊, 1 / 2 * ((Λ n : ℝ) * Real.log (Y / n))
      ≤ ∑ n ∈ Finset.Icc 2 ⌊Y⌋₊, (Λ n : ℝ) / Real.sqrt n *
          (2 * packetAutocorr (evenPolar a δ) (Real.log n)) := by
        refine Finset.sum_le_sum fun n hn => ?_
        have hn2 := (Finset.mem_Icc.mp hn).1
        have hn0 : 0 < n := by omega
        have hnr : (0 : ℝ) < n := by exact_mod_cast hn0
        have hnY : (n : ℝ) ≤ Y := (Nat.cast_le.mpr (Finset.mem_Icc.mp hn).2).trans
          (Nat.floor_le (Real.exp_pos _).le)
        have hlogY : Real.log n ≤ 2 * a - 2 * δ := by
          calc Real.log n ≤ Real.log Y := Real.log_le_log hnr hnY
            _ = 2 * a - 2 * δ := Real.log_exp _
        have hlog0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
        have hge := packetAutocorr_evenPolar_ge (a := a) hδ hlog0 (by linarith)
        have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnr
        have hexp : Real.exp (Real.log n / 2) = Real.sqrt n := by
          have h := exp_add_half_log hn0 0
          rwa [zero_add, Real.exp_zero, one_mul] at h
        rw [hexp] at hge
        have hlogdiv : Real.log (Y / n) = 2 * a - 2 * δ - Real.log n := by
          rw [Real.log_div (Real.exp_pos _).ne' hnr.ne', hY, Real.log_exp]
        rw [hlogdiv]
        have hΛ : 0 ≤ (Λ n : ℝ) / Real.sqrt n :=
          div_nonneg ArithmeticFunction.vonMangoldt_nonneg hs.le
        have hmul := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hge (by norm_num : (0 : ℝ) ≤ 2)) hΛ
        have e : (Λ n : ℝ) / Real.sqrt n *
            (2 * (Real.sqrt n / 4 * (2 * a - 2 * δ - Real.log n))) =
            1 / 2 * ((Λ n : ℝ) * (2 * a - 2 * δ - Real.log n)) := by
          field_simp
          ring
        rwa [e] at hmul
    _ ≤ ∑ n ∈ Finset.Icc 2 N, (Λ n : ℝ) / Real.sqrt n *
          (2 * packetAutocorr (evenPolar a δ) (Real.log n)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => by
          rw [Finset.mem_Icc] at hn ⊢
          omega) fun n _ _ => hT n

/-- **The odd polar packet anticorrelates with the primes.** Its contact form with `Λ` is at most
`4a e^{a} Σ_{n ≤ e^{2a}} Λ(n)/n` minus that of the even polar packet. -/
theorem contactForm_oddPolar_le {a δ : ℝ} (ha : 0 ≤ a) (hδ : 0 < δ) :
    contactForm (fun n => Λ n) (fun u => (oddPolar a δ u : ℂ)) ⌊Real.exp (2 * a)⌋₊ ≤
      4 * a * Real.exp a * (∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, (Λ n : ℝ) / n) -
        contactForm (fun n => Λ n) (fun u => (evenPolar a δ u : ℂ)) ⌊Real.exp (2 * a)⌋₊ := by
  rw [contactForm_packet, contactForm_packet, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun n hn => ?_
  have hn2 := (Finset.mem_Icc.mp hn).1
  have hn0 : 0 < n := by omega
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn0
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnr
  have hss : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hnr.le
  have hle := packetAutocorr_oddPolar_le (δ := δ) ha hδ (Real.log n)
  rw [exp_sub_half_log hn0 a] at hle
  have hΛ : 0 ≤ (Λ n : ℝ) / Real.sqrt n :=
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg hs.le
  have hmul := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hle (by norm_num : (0 : ℝ) ≤ 2)) hΛ
  have e : (Λ n : ℝ) / Real.sqrt n *
      (2 * (2 * a * (Real.exp a / Real.sqrt n) -
        packetAutocorr (evenPolar a δ) (Real.log n))) =
      4 * a * Real.exp a * ((Λ n : ℝ) / n) -
        (Λ n : ℝ) / Real.sqrt n * (2 * packetAutocorr (evenPolar a δ) (Real.log n)) := by
    rw [← hss]
    field_simp
    ring
  rwa [e] at hmul

/-! ### The balance of a polar packet -/

/-- The arithmetic of the balance: with `E = e^{a}`, a mass `M ≤ a + E/2`, a conductor
`x ≤ κ₂ E` and a polynomial budget below `(κ₁ − κ₂) E / 2`, the upper bound of the form of a
polar packet is negative. -/
theorem polar_balance {a E x K κ₁ κ₂ M : ℝ} (ha : 1 ≤ a) (hE : 0 < E) (haE : a ≤ E)
    (hx0 : 0 ≤ x) (hx : x ≤ κ₂ * E) (hκ₂0 : 0 ≤ κ₂) (hκ₂ : κ₂ ≤ 1) (hM0 : 0 ≤ M)
    (hM : M ≤ a + E / 2) (hK : 0 ≤ K)
    (hbig : (3 / 2 * (5 + K) + 41) * (1 + a) ^ 3 < (κ₁ - κ₂) / 2 * E) :
    (5 + x + K) * M + 4 * a * E * (2 + 2 * a) ^ 2 + 4 * (2 + 2 * a) ^ 2 * M -
      κ₁ / 2 * E ^ 2 < 0 := by
  have ha0 : 0 ≤ a := by linarith
  have hM' : M ≤ 3 / 2 * E := by linarith
  have hc0 : 0 ≤ 5 + K + 4 * (2 + 2 * a) ^ 2 := by positivity
  have h1 : (5 + K + 4 * (2 + 2 * a) ^ 2) * M ≤ (5 + K + 4 * (2 + 2 * a) ^ 2) * (3 / 2 * E) :=
    mul_le_mul_of_nonneg_left hM' hc0
  have h2 : x * M ≤ κ₂ * E * (a + E / 2) :=
    mul_le_mul hx hM hM0 (mul_nonneg hκ₂0 hE.le)
  have h3 : κ₂ * E * (a + E / 2) ≤ a * E + κ₂ / 2 * E ^ 2 := by
    nlinarith [mul_nonneg (mul_nonneg ha0 hE.le) (sub_nonneg.mpr hκ₂)]
  -- the polynomial budget
  have hs1 : (1 : ℝ) ≤ (1 + a) ^ 3 := one_le_pow₀ (by linarith)
  have hs2 : (1 + a) ^ 2 ≤ (1 + a) ^ 3 :=
    pow_le_pow_right₀ (by linarith) (by norm_num)
  have hs3 : a * (1 + a) ^ 2 ≤ (1 + a) ^ 3 := by
    have : (1 + a) ^ 3 = (1 + a) * (1 + a) ^ 2 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  have hs4 : a ≤ (1 + a) ^ 3 := by nlinarith
  have h4 : 3 / 2 * (5 + K + 4 * (2 + 2 * a) ^ 2) + a + 4 * a * (2 + 2 * a) ^ 2 ≤
      (3 / 2 * (5 + K) + 41) * (1 + a) ^ 3 := by
    have e1 : (2 + 2 * a) ^ 2 = 4 * (1 + a) ^ 2 := by ring
    rw [e1]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 5 + K) (sub_nonneg.mpr hs1)]
  have h5 := mul_lt_mul_of_pos_right hbig hE
  have h6 := mul_le_mul_of_nonneg_right h4 hE.le
  nlinarith

/-- A cubic is eventually below an exponential. -/
theorem eventually_cubic_lt_exp (C : ℝ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ a : ℝ in atTop, C * (1 + a) ^ 3 < c * Real.exp a := by
  have hD : 0 < 8 * (|C| + 1) := by positivity
  have ht := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 3
  filter_upwards [ht.eventually (Iio_mem_nhds (div_pos hc hD)), eventually_ge_atTop (1 : ℝ)]
    with a ha ha1
  have hexp : 0 < Real.exp a := Real.exp_pos a
  have h1 : a ^ 3 < c / (8 * (|C| + 1)) * Real.exp a := by
    have h := mul_lt_mul_of_pos_right ha hexp
    rwa [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one] at h
  have h2 : (1 + a) ^ 3 ≤ 8 * a ^ 3 := by
    have : 1 + a ≤ 2 * a := by linarith
    calc (1 + a) ^ 3 ≤ (2 * a) ^ 3 := pow_le_pow_left₀ (by linarith) this 3
      _ = 8 * a ^ 3 := by ring
  have h3 : C * (1 + a) ^ 3 ≤ (|C| + 1) * (8 * a ^ 3) :=
    mul_le_mul ((le_abs_self C).trans (by linarith)) h2 (by positivity) (by positivity)
  have h4 : (|C| + 1) * (8 * a ^ 3) < (|C| + 1) * (8 * (c / (8 * (|C| + 1)) * Real.exp a)) :=
    mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left h1 (by norm_num)) (by positivity)
  have e : (|C| + 1) * (8 * (c / (8 * (|C| + 1)) * Real.exp a)) = c * Real.exp a := by
    field_simp
  linarith

/-! ### The three fakes -/

/-- **Beyond the trivial aperture the polar packets detect the fakes.** For every `η > 0` and
every conductor with `log q` large, at every aperture `a ≥ log log q + η`: the form of `Λ`
without pole plane is negative on the even polar packet, and the forms of `−Λ` and of the
Liouville twist are negative on the odd polar packet. -/
theorem exists_systemForm_polar_neg {η : ℝ} (hη : 0 < η) :
    ∃ M₀ : ℝ, 1 ≤ M₀ ∧ ∀ q : ℝ, M₀ ≤ Real.log q → ∀ a : ℝ, Real.log (Real.log q) + η ≤ a →
      systemForm (fun n => Λ n) q a (fun u => (evenPolar a (η / 8) u : ℂ)) < 0 ∧
      systemForm (fun n => -Λ n) q a (fun u => (oddPolar a (η / 8) u : ℂ)) < 0 ∧
      systemForm liouvilleWeight q a (fun u => (oddPolar a (η / 8) u : ℂ)) < 0 := by
  obtain ⟨S, -, hS⟩ := exists_abs_deriv_smoothTransition_le
  set δ := η / 8 with hδdef
  have hδ : 0 < δ := by positivity
  set K := (1 / 2 + 2 * S / δ) ^ 2 with hKdef
  have hK : 0 ≤ K := sq_nonneg _
  -- the constants of the prime number theorem
  have hη'0 : 0 < 1 - Real.exp (-η / 4) := by
    have : Real.exp (-η / 4) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
    rw [Real.exp_zero] at this
    linarith
  have hη'1 : 1 - Real.exp (-η / 4) ≤ 1 := by linarith [Real.exp_pos (-η / 4)]
  obtain ⟨Y₀, hY₀1, hY₀⟩ := exists_riesz_ge hη'0 hη'1
  have hκ : 0 < (Real.exp (-η / 2) - Real.exp (-η)) / 2 := by
    have : Real.exp (-η) < Real.exp (-η / 2) := Real.exp_lt_exp.mpr (by linarith)
    linarith
  obtain ⟨a₁, ha₁⟩ := eventually_atTop.mp (eventually_cubic_lt_exp (3 / 2 * (5 + K) + 41) hκ)
  set a₀ := max (max a₁ 1) (Real.log Y₀ / 2 + δ) with ha₀def
  refine ⟨Real.exp a₀, ?_, fun q hq a haq => ?_⟩
  · exact Real.one_le_exp ((le_max_right a₁ 1).trans (le_max_left _ _) |>.trans' zero_le_one)
  set x := Real.log q with hxdef
  have hx0 : 0 < x := (Real.exp_pos a₀).trans_le hq
  have hlogx : a₀ ≤ Real.log x := by
    rw [← Real.log_exp a₀]
    exact Real.log_le_log (Real.exp_pos _) hq
  have haa₀ : a₀ ≤ a := by linarith
  have ha1 : 1 ≤ a := ((le_max_right a₁ 1).trans (le_max_left _ _)).trans haa₀
  have ha0 : 0 ≤ a := by linarith
  have haY : Real.log Y₀ / 2 + δ ≤ a := (le_max_right _ _).trans haa₀
  set E := Real.exp a with hEdef
  have hE : 0 < E := Real.exp_pos a
  have haE : a ≤ E := by linarith [Real.add_one_le_exp a]
  -- the conductor is below `e^{−η} e^{a}`
  have hxE : x ≤ Real.exp (-η) * E := by
    have h1 : Real.exp (Real.log x) ≤ Real.exp (a - η) := Real.exp_le_exp.mpr (by linarith)
    rw [Real.exp_log hx0] at h1
    have h2 : Real.exp (a - η) = Real.exp (-η) * E := by
      rw [hEdef, ← Real.exp_add]
      congr 1
      ring
    linarith
  -- the mass of a polar packet
  set Mb := a + Real.sinh a with hMb
  have hsinh : Real.sinh a ≤ E / 2 := by
    rw [Real.sinh_eq]
    linarith [Real.exp_pos (-a)]
  have hsinh0 : 0 ≤ Real.sinh a := Real.sinh_nonneg_iff.mpr ha0
  have hMb0 : 0 ≤ Mb := by linarith
  have hMbE : Mb ≤ a + E / 2 := by linarith
  -- the Riesz mean at `Y = e^{2a − 2δ}`
  have hY : Y₀ ≤ Real.exp (2 * a - 2 * δ) := by
    have h1 : Real.log Y₀ ≤ 2 * a - 2 * δ := by linarith
    calc Y₀ = Real.exp (Real.log Y₀) := (Real.exp_log (by linarith)).symm
      _ ≤ Real.exp (2 * a - 2 * δ) := Real.exp_le_exp.mpr h1
  have hriesz := (hY₀ _ hY).trans_eq' (by
    show Real.exp (-η / 2) * E ^ 2 = (1 - (1 - Real.exp (-η / 4))) * Real.exp (2 * a - 2 * δ)
    rw [hEdef, hδdef, sub_sub_cancel, ← Real.exp_add, sq, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring)
  have hCE := (mul_le_mul_of_nonneg_left hriesz (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans
    (contactForm_evenPolar_ge (a := a) hδ)
  -- Mertens
  have hmer := sum_vonMangoldt_div_window_le ha0
  have hmer2 : ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, (Λ n : ℝ) / n ≤ (2 + 2 * a) ^ 2 :=
    (Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => by
      rw [Finset.mem_Icc] at hn ⊢
      omega) fun n _ _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (Nat.cast_nonneg n)).trans hmer
  have hCO := contactForm_oddPolar_le (δ := δ) ha0 hδ
  have hCO' : contactForm (fun n => Λ n) (fun u => (oddPolar a δ u : ℂ))
        ⌊Real.exp (2 * a)⌋₊ ≤
      4 * a * E * (2 + 2 * a) ^ 2 - Real.exp (-η / 2) / 2 * E ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hmer2 (by positivity : (0 : ℝ) ≤ 4 * a * E)
    linarith
  -- the balance
  have hbal := polar_balance (K := K) (κ₁ := Real.exp (-η / 2)) (κ₂ := Real.exp (-η))
    (M := Mb) ha1 hE haE hx0.le hxE (Real.exp_pos _).le
    (Real.exp_le_one_iff.mpr (by linarith)) hMb0 hMbE hK
    (by
      have h := ha₁ a (((le_max_left a₁ 1).trans (le_max_left _ _)).trans haa₀)
      rwa [hEdef])
  have h5x : 0 ≤ 5 + x := by linarith
  have hpos1 : 0 ≤ 4 * a * E * (2 + 2 * a) ^ 2 := by positivity
  have hpos2 : 0 ≤ 4 * (2 + 2 * a) ^ 2 * Mb := by positivity
  -- masses and derivative energies
  have hME := integral_evenPolar_sq_le ha0 hδ
  have hMO := integral_oddPolar_sq_le ha0 hδ
  have hDE := integral_deriv_evenPolar_sq_le hS ha0 hδ
  have hDO := integral_deriv_oddPolar_sq_le hS ha0 hδ
  have hE0 : ∀ u, a ≤ |u| → evenPolar a δ u = 0 := fun u hu => evenPolar_eq_zero hδ hu
  have hO0 : ∀ u, a ≤ |u| → oddPolar a δ u = 0 := fun u hu => oddPolar_eq_zero hδ hu
  refine ⟨?_, ?_, ?_⟩
  · -- `Λ` without pole plane, on the even polar packet
    have h := systemForm_le_of_packet (contDiff_evenPolar a δ) hE0 (fun n => Λ n) q
    have hm := mul_le_mul_of_nonneg_left hME h5x
    nlinarith
  · -- `−Λ`, on the odd polar packet
    have h := systemForm_le_of_packet (contDiff_oddPolar a δ) hO0 (fun n => -Λ n) q
    rw [contactForm_neg] at h
    have hm := mul_le_mul_of_nonneg_left hMO h5x
    nlinarith
  · -- the Liouville twist, on the odd polar packet
    have h := systemForm_le_of_packet (contDiff_oddPolar a δ) hO0 liouvilleWeight q
    rw [contactForm_liouvilleWeight] at h
    have hsq := (abs_le.mp (abs_contactForm_squareWeight_le (contDiff_oddPolar a δ).continuous
      (hasCompactSupport_oddPolar hδ) ⌊Real.exp (2 * a)⌋₊)).1
    have hsq' : 2 * (∑ m ∈ Finset.Icc 1 ⌊Real.exp (2 * a)⌋₊, (Λ m : ℝ) / m) *
        (∫ u, oddPolar a δ u ^ 2) ≤ 2 * (2 + 2 * a) ^ 2 * Mb :=
      mul_le_mul (mul_le_mul_of_nonneg_left hmer (by norm_num)) hMO
        (integral_nonneg fun _ => sq_nonneg _) (by positivity)
    have hm := mul_le_mul_of_nonneg_left hMO h5x
    nlinarith

/-- **Three dominated systems are infeasible beyond the trivial aperture.** -/
theorem exists_not_feasible {η : ℝ} (hη : 0 < η) :
    ∃ M₀ : ℝ, 1 ≤ M₀ ∧ ∀ q : ℝ, M₀ ≤ Real.log q → ∀ a : ℝ, Real.log (Real.log q) + η ≤ a →
      ¬ Feasible q a liouvilleWeight ∧ ¬ Feasible q a (fun n => -Λ n) ∧
        ¬ Feasible q a (fun n => Λ n) := by
  obtain ⟨M₀, hM₀1, hM₀⟩ := exists_systemForm_polar_neg hη
  refine ⟨M₀, hM₀1, fun q hq a ha => ?_⟩
  have hδ : 0 < η / 8 := by positivity
  obtain ⟨h1, h2, h3⟩ := hM₀ q hq a ha
  have hEc : ContDiff ℝ 2 fun u => (evenPolar a (η / 8) u : ℂ) :=
    contDiff_ofReal_packet ((contDiff_evenPolar a (η / 8)).of_le (by norm_num))
  have hOc : ContDiff ℝ 2 fun u => (oddPolar a (η / 8) u : ℂ) :=
    contDiff_ofReal_packet ((contDiff_oddPolar a (η / 8)).of_le (by norm_num))
  have hEs : tsupport (fun u => (evenPolar a (η / 8) u : ℂ)) ⊆ Set.Icc (-a) a :=
    tsupport_ofReal_subset_of_eq_zero fun u hu => evenPolar_eq_zero hδ hu
  have hOs : tsupport (fun u => (oddPolar a (η / 8) u : ℂ)) ⊆ Set.Icc (-a) a :=
    tsupport_ofReal_subset_of_eq_zero fun u hu => oddPolar_eq_zero hδ hu
  exact ⟨fun hF => absurd (hF _ hOc hOs) (not_le.mpr h3),
    fun hF => absurd (hF _ hOc hOs) (not_le.mpr h2),
    fun hF => absurd (hF _ hEc hEs) (not_le.mpr h1)⟩

/-! ### The trivial aperture -/

/-- The trivial aperture of a conductor: the supremum of the apertures at which every dominated
system is feasible. -/
def trivialAperture (q : ℝ) : ℝ :=
  sSup {a : ℝ | 0 ≤ a ∧ ∀ w : ℕ → ℝ, Dominated w → Feasible q a w}

/-- **The ladder of the conductor has no gap.** For every `η > 0` and every conductor with
`log q` large, the trivial aperture lies within `η` of `log log q`. -/
theorem exists_abs_trivialAperture_sub_le {η : ℝ} (hη : 0 < η) :
    ∃ M₀ : ℝ, ∀ q : ℝ, M₀ ≤ Real.log q →
      |trivialAperture q - Real.log (Real.log q)| ≤ η := by
  obtain ⟨M₁, hM₁⟩ := exists_systemForm_margin hη
  obtain ⟨M₂, hM₂1, hM₂⟩ := exists_not_feasible hη
  refine ⟨max (max M₁ M₂) (Real.exp η), fun q hq => ?_⟩
  have hq1 : M₁ ≤ Real.log q := ((le_max_left _ _).trans (le_max_left _ _)).trans hq
  have hq2 : M₂ ≤ Real.log q := ((le_max_right _ _).trans (le_max_left _ _)).trans hq
  have hq3 : Real.exp η ≤ Real.log q := (le_max_right _ _).trans hq
  have hx0 : 0 < Real.log q := (Real.exp_pos η).trans_le hq3
  have hll : η ≤ Real.log (Real.log q) := by
    rw [← Real.log_exp η]
    exact Real.log_le_log (Real.exp_pos _) hq3
  set A := {a : ℝ | 0 ≤ a ∧ ∀ w : ℕ → ℝ, Dominated w → Feasible q a w} with hA
  -- every aperture of the set is below `log log q + η`
  have hup : ∀ a ∈ A, a ≤ Real.log (Real.log q) + η := fun a ha => by
    by_contra hlt
    push Not at hlt
    exact (hM₂ q hq2 a hlt.le).1 (ha.2 _ dominated_liouvilleWeight)
  -- the aperture `log log q − η` belongs to the set
  have hmem : Real.log (Real.log q) - η ∈ A := by
    refine ⟨by linarith, fun w hw F hF hFs => ?_⟩
    have hδ : 0 ≤ 1 - Real.exp (-η / 2) := by
      have : Real.exp (-η / 2) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
      rw [Real.exp_zero] at this
      linarith
    exact le_trans (mul_nonneg (mul_nonneg (by linarith) hx0.le)
      (integral_nonneg fun _ => sq_nonneg _))
      (hM₁ q hq1 _ (by linarith) le_rfl hw hF hFs)
  have hbdd : BddAbove A := ⟨_, hup⟩
  have h1 : Real.log (Real.log q) - η ≤ trivialAperture q := le_csSup hbdd hmem
  have h2 : trivialAperture q ≤ Real.log (Real.log q) + η := csSup_le ⟨_, hmem⟩ hup
  rw [abs_le]
  constructor <;> linarith

/-- **The trivial aperture of a conductor is `log log q + o(1)`.** -/
theorem tendsto_trivialAperture_sub_log :
    Tendsto (fun x : ℝ => trivialAperture (Real.exp x) - Real.log x) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨M₀, hM₀⟩ := exists_abs_trivialAperture_sub_le (half_pos hε)
  refine ⟨M₀, fun x hx => ?_⟩
  have h := hM₀ (Real.exp x) (by rwa [Real.log_exp])
  rw [Real.log_exp] at h
  rw [Real.dist_eq, sub_zero]
  linarith

end GaloisForLFunctions.SelectiveArithmetic
