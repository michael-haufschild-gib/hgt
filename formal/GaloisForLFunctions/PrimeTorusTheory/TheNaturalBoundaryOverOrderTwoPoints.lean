import GaloisForLFunctions.PrimeTorusTheory.TheHullOverOrderTwoPoints
import GaloisForLFunctions.PrimeTorusTheory.TheNaturalBoundaryOfTheHull

/-!
# The natural boundary over order-two points

For almost every order-two point the fibre extends zero-free to `Re s > ½` (`ae_signFibre_extends_zeroFree`). As over a Haar-typical point, this is sharp at every point of the line.

**Theorem** (`ae_sign_natural_boundary`). For almost every order-two point, the zero-free extension of `Σ_n X_n n^{−s}` to `Re s > ½` has no analytic continuation across any point of `Re s = ½`.

**Mechanism.** The coins are lacunary (`isLacunary_sign`): `E[X_p X_q] = δ_{pq}` and, over pairs `p < q`, the products `X_p X_q` are orthonormal, since `p q' = q p'` with `p < q`, `p' < q'` forces `(p, q) = (p', q')` (`integral_pair_sign`). So Zygmund's theorem applies to the prime sum.

The new feature is the quadratic part of the logarithm. Over an order-two point `X_p² = 1`, so `Σ_p (X_p p^{−s})²/2 = ½ P(2s)` is deterministic, where `P(w) = Σ_p p^{−w}` is the prime zeta function. It is not small in `L²`; it is bounded along every ray ending at `½ + iq`, `q ≠ 0` (`exists_bound_primeZeta`). Indeed `P = log ζ − h` with `h` analytic on `Re w > ½`, so `P' = ζ'/ζ − h'`, which is bounded near `1 + 2iq` because `ζ(1 + 2iq) ≠ 0`. The rays used in the boundary argument end at nonzero rational heights (`no_continuation_of_rays`), and there the remainder is bounded, so the argument of the Haar case goes through.
-/

open MeasureTheory Filter Topology Metric GaloisForLFunctions.HTGeometry
open _root_.RHTower.SteinhausModel

namespace GaloisForLFunctions.PrimeTorusTheory

noncomputable section

open GaloisForLFunctions.RHTower

local notation "conj" => starRingEnd ℂ

/-! ### Orthogonality under the coins -/

theorem integral_charFactor_coin (k : ℤ) :
    ∫ y, charFactor k y ∂coin = if Even k then 1 else 0 := by
  have hc : Continuous (charFactor k) := by
    unfold charFactor
    fun_prop
  have hn : ∀ y, ‖charFactor k y‖ ≤ 1 := fun y => by
    unfold charFactor
    rw [show ((2 * Real.pi : ℝ) : ℂ) * Complex.I * (((k : ℝ) * y : ℝ) : ℂ) =
      ((2 * Real.pi * ((k : ℝ) * y) : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  rw [integral_coin hc.measurable hn]
  have h0 : charFactor k 0 = 1 := by simp [charFactor]
  have h1 : charFactor k (1 / 2) = (-1) ^ k := by
    unfold charFactor
    rw [show ((2 * Real.pi : ℝ) : ℂ) * Complex.I * (((k : ℝ) * (1 / 2) : ℝ) : ℂ) =
      (k : ℂ) * (Real.pi * Complex.I) by push_cast; ring, Complex.exp_int_mul, Complex.exp_pi_mul_I]
  rw [h0, h1]
  rcases Int.even_or_odd k with h | h
  · rw [if_pos h, h.neg_one_zpow]
    norm_num
  · rw [if_neg (Int.not_even_iff_odd.mpr h), h.neg_one_zpow]
    norm_num

/-- Under the coins, `E[X_n conj X_m]` is `1` when every exponent of `n/m` is even and `0` otherwise. -/
theorem integral_X_mul_conj_sign (n m : ℕ) :
    ∫ ω, X n ω * conj (X m ω) ∂signMeasure =
      ∏ p ∈ n.primeFactors ∪ m.primeFactors, (if Even (freq n m p) then (1 : ℂ) else 0) := by
  classical
  set s := n.primeFactors ∪ m.primeFactors with hs
  have hstep1 : ∫ ω, X n ω * conj (X m ω) ∂signMeasure
      = ∫ ω, ∏ p ∈ s, charFactor (freq n m p) (ω p) ∂signMeasure := by
    apply integral_congr_ae
    filter_upwards with ω
    exact X_mul_conj_eq_prod ω
  have hcont : Continuous fun y : (i : ↥s) → ℝ => ∏ i : ↥s, charFactor (freq n m ↑i) (y i) := by
    apply continuous_finsetProd
    intro i _
    exact (Complex.continuous_exp.comp (by continuity : Continuous fun t : ℝ =>
      ((2 * Real.pi : ℝ) : ℂ) * Complex.I * (((freq n m ↑i : ℝ) * t : ℝ) : ℂ))).comp (continuous_apply i)
  have hmap : Measure.map s.restrict signMeasure = Measure.pi fun _ : ↥s => coin := by
    unfold signMeasure
    exact Measure.infinitePi_map_restrict _
  have hstep2 : ∫ ω, ∏ p ∈ s, charFactor (freq n m p) (ω p) ∂signMeasure
      = ∫ y : (i : ↥s) → ℝ, ∏ i : ↥s, charFactor (freq n m ↑i) (y i)
          ∂(Measure.pi fun _ : ↥s => coin) := by
    rw [← hmap, integral_map (Finset.measurable_restrict s).aemeasurable hcont.aestronglyMeasurable]
    apply integral_congr_ae
    filter_upwards with ω
    rw [← Finset.prod_coe_sort s (fun p => charFactor (freq n m p) (ω p))]
    rfl
  rw [hstep1, hstep2, integral_fintype_prod_eq_prod fun (i : ↥s) (t : ℝ) => charFactor (freq n m ↑i) t,
    ← Finset.prod_coe_sort s (fun p => if Even (freq n m p) then (1 : ℂ) else 0)]
  exact Finset.prod_congr rfl fun i _ => integral_charFactor_coin _

theorem factorization_prime_apply {p : ℕ} (hp : p.Prime) (r : ℕ) :
    p.factorization r = if p = r then 1 else 0 := by
  rw [hp.factorization, Finsupp.single_apply]

theorem factorization_mul_primes {a d : ℕ} (ha : a.Prime) (hd : d.Prime) (r : ℕ) :
    (a * d).factorization r = (if a = r then 1 else 0) + (if d = r then 1 else 0) := by
  rw [Nat.factorization_mul ha.ne_zero hd.ne_zero, Finsupp.add_apply, factorization_prime_apply ha,
    factorization_prime_apply hd]

/-- The coins at distinct primes are orthogonal. -/
theorem integral_X_prime_mul_conj_sign {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    ∫ ω, X p ω * conj (X q ω) ∂signMeasure = if p = q then 1 else 0 := by
  by_cases h : p = q
  · subst h
    have h1 : ∀ ω, X p ω * conj (X p ω) = 1 := fun ω => by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_X]
      simp
    simp [h1]
  · rw [if_neg h, integral_X_mul_conj_sign]
    refine Finset.prod_eq_zero (i := p)
      (Finset.mem_union_left _ (by rw [hp.primeFactors]; exact Finset.mem_singleton_self p)) ?_
    rw [if_neg]
    unfold freq
    rw [factorization_prime_apply hp, factorization_prime_apply hq, Int.even_iff]
    split_ifs <;> omega

/-- **Pair products over `p < q` are orthonormal under the coins.** -/
theorem integral_pair_sign {a b c d : ℕ} (ha : a.Prime) (hb : b.Prime) (hc : c.Prime) (hd : d.Prime)
    (hab : a < b) (hcd : c < d) :
    ∫ ω, (X a ω * conj (X b ω)) * conj (X c ω * conj (X d ω)) ∂signMeasure =
      if (a, b) = (c, d) then 1 else 0 := by
  have e : ∀ ω, (X a ω * conj (X b ω)) * conj (X c ω * conj (X d ω)) =
      X (a * d) ω * conj (X (b * c) ω) := by
    intro ω
    rw [X_mul ha.ne_zero hd.ne_zero, X_mul hb.ne_zero hc.ne_zero]
    simp only [map_mul, Complex.conj_conj]
    ring
  simp_rw [e]
  by_cases hβ : (a, b) = (c, d)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hβ
    have h1 : ∀ ω, X (a * b) ω * conj (X (b * a) ω) = 1 := fun ω => by
      rw [mul_comm b a, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_X]
      simp
    simp [h1]
  · rw [if_neg hβ, integral_X_mul_conj_sign]
    have hmem : ∀ {u v : ℕ}, u.Prime → v.Prime → u ∈ (u * v).primeFactors := fun hu hv =>
      Nat.mem_primeFactors.mpr ⟨hu, dvd_mul_right _ _, Nat.mul_ne_zero hu.ne_zero hv.ne_zero⟩
    by_cases hac : a = c
    · subst hac
      have hbd : b ≠ d := fun h => hβ (by rw [h])
      refine Finset.prod_eq_zero (i := b) (Finset.mem_union_right _ (hmem hb ha)) ?_
      rw [if_neg]
      unfold freq
      rw [factorization_mul_primes ha hd, factorization_mul_primes hb ha, Int.even_iff]
      split_ifs <;> omega
    · by_cases had : a = d
      · refine Finset.prod_eq_zero (i := b) (Finset.mem_union_right _ (hmem hb hc)) ?_
        rw [if_neg]
        unfold freq
        rw [factorization_mul_primes ha hd, factorization_mul_primes hb hc, Int.even_iff]
        split_ifs <;> omega
      · refine Finset.prod_eq_zero (i := a) (Finset.mem_union_left _ (hmem ha hd)) ?_
        rw [if_neg]
        unfold freq
        rw [factorization_mul_primes ha hd, factorization_mul_primes hb hc, Int.even_iff]
        split_ifs <;> omega

/-- An orthonormal family has `∫ |Σ a_n x_n|² = Σ |a_n|²`. -/
theorem integral_normSq_of_orthonormal {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {x : ℕ → Ω → ℂ} (hm : ∀ n, Measurable (x n)) {s : Finset ℕ}
    (hb : ∀ n ∈ s, ∀ ω, ‖x n ω‖ ≤ 1)
    (horth : ∀ m ∈ s, ∀ n ∈ s, ∫ ω, x m ω * conj (x n ω) ∂μ = if m = n then 1 else 0)
    (a : ℕ → ℂ) : ∫ ω, ‖∑ n ∈ s, a n * x n ω‖ ^ 2 ∂μ = ∑ n ∈ s, ‖a n‖ ^ 2 := by
  have hexp : ∀ ω, ((‖∑ n ∈ s, a n * x n ω‖ ^ 2 : ℝ) : ℂ) =
      ∑ m ∈ s, ∑ n ∈ s, a m * conj (a n) * (x m ω * conj (x n ω)) := by
    intro ω
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
    simp only [map_mul]
    ring
  have hi : ∀ m ∈ s, ∀ n ∈ s, Integrable (fun ω => a m * conj (a n) * (x m ω * conj (x n ω))) μ := by
    intro m hm' n hn
    refine integrable_of_bound (measurable_const.mul ((hm m).mul
      (Complex.continuous_conj.measurable.comp (hm n)))) (C := ‖a m‖ * ‖a n‖) fun ω => ?_
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj]
    have h1 := hb m hm' ω
    have h2 := hb n hn ω
    have h3 : ‖x m ω‖ * ‖x n ω‖ ≤ 1 := by nlinarith [norm_nonneg (x m ω), norm_nonneg (x n ω)]
    nlinarith [mul_nonneg (norm_nonneg (a m)) (norm_nonneg (a n))]
  have hc : ((∫ ω, ‖∑ n ∈ s, a n * x n ω‖ ^ 2 ∂μ : ℝ) : ℂ) = ((∑ n ∈ s, ‖a n‖ ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    simp_rw [hexp]
    rw [integral_finsetSum _ fun m hm' => integrable_finsetSum _ fun n hn => hi m hm' n hn]
    push_cast
    refine Finset.sum_congr rfl fun m hm' => ?_
    rw [integral_finsetSum _ fun n hn => hi m hm' n hn]
    have hterm : ∀ n ∈ s, ∫ ω, a m * conj (a n) * (x m ω * conj (x n ω)) ∂μ =
        if m = n then a m * conj (a n) else 0 := by
      intro n hn
      rw [integral_const_mul, horth m hm' n hn]
      split_ifs <;> simp
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq s m, if_pos hm', Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  exact_mod_cast hc

/-- **Bessel for the coins.** Over ordered pairs the correlations have square sum at most twice the measure: each unordered pair is counted twice. -/
theorem bessel_sign (E : Set Omega) (Ps : Finset ℕ) (hPs : ∀ p ∈ Ps, p.Prime) :
    ∑ α ∈ Ps.offDiag, ‖∫ ω in E, X α.1 ω * conj (X α.2 ω) ∂signMeasure‖ ^ 2 ≤
      2 * (signMeasure E).toReal := by
  classical
  set c : ℕ × ℕ → ℝ := fun α => ‖∫ ω in E, X α.1 ω * conj (X α.2 ω) ∂signMeasure‖ ^ 2 with hc
  have hswap : ∀ α : ℕ × ℕ, c α.swap = c α := fun α => by
    simp only [hc, Prod.fst_swap, Prod.snd_swap]
    have h1 : (fun ω => X α.2 ω * conj (X α.1 ω)) = fun ω => conj (X α.1 ω * conj (X α.2 ω)) := by
      funext ω
      simp only [map_mul, Complex.conj_conj]
      ring
    rw [h1, integral_conj, Complex.norm_conj]
  set L := Ps.offDiag.filter fun α => α.1 < α.2 with hL
  have hsplit : ∑ α ∈ Ps.offDiag, c α =
      ∑ α ∈ L, c α + ∑ α ∈ Ps.offDiag.filter (fun α => ¬ α.1 < α.2), c α :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hG : ∑ α ∈ Ps.offDiag.filter (fun α => ¬ α.1 < α.2), c α = ∑ α ∈ L, c α := by
    refine Finset.sum_nbij' Prod.swap Prod.swap (fun α hα => ?_) (fun α hα => ?_)
      (fun α _ => Prod.swap_swap α) (fun α _ => Prod.swap_swap α) fun α _ => (hswap α).symm
    · obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hα
      obtain ⟨h3, h4, h5⟩ := Finset.mem_offDiag.mp h1
      refine Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr ⟨h4, h3, Ne.symm h5⟩, ?_⟩
      show α.2 < α.1
      omega
    · obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hα
      obtain ⟨h3, h4, h5⟩ := Finset.mem_offDiag.mp h1
      refine Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr ⟨h4, h3, Ne.symm h5⟩, ?_⟩
      show ¬ α.2 < α.1
      omega
  have hbes := bessel_of_orthonormal (μ := signMeasure) L
    (f := fun α ω => X α.1 ω * conj (X α.2 ω))
    (fun α => (measurable_X _).mul (Complex.continuous_conj.measurable.comp (measurable_X _)))
    (fun α ω => by rw [norm_mul, Complex.norm_conj, norm_X, norm_X, one_mul])
    (fun β hβ γ hγ => by
      obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hβ
      obtain ⟨h3, h4⟩ := Finset.mem_filter.mp hγ
      obtain ⟨h5, h6, -⟩ := Finset.mem_offDiag.mp h1
      obtain ⟨h7, h8, -⟩ := Finset.mem_offDiag.mp h3
      have := integral_pair_sign (hPs _ h5) (hPs _ h6) (hPs _ h7) (hPs _ h8) h2 h4
      simpa only [Prod.mk.eta] using this) E
  rw [hsplit, hG]
  linarith

/-- **The coins are lacunary.** -/
theorem isLacunary_sign : IsLacunary signMeasure fun n ω => X n ω where
  measurable n := measurable_X n
  norm_eq_one p _ ω := norm_X p ω
  integral_normSq _ a hs := integral_normSq_of_orthonormal measurable_X (fun n _ ω => (norm_X n ω).le)
    (fun m hm n hn => integral_X_prime_mul_conj_sign (hs m hm) (hs n hn)) a
  bessel E Ps hPs := bessel_sign E Ps hPs

/-! ### The prime zeta function near the line -/

theorem orbitPoint_zero_apply {n : ℕ} (hn : n ≠ 0) : orbitPoint 0 n = 1 := by
  show (if n = 0 then (0 : ℂ) else (n : ℂ) ^ (-(((0 : ℝ) : ℂ) * Complex.I))) = 1
  rw [if_neg hn]
  simp

theorem norm_orbitPoint_zero_prime : ∀ p, p.Prime → ‖orbitPoint 0 p‖ = 1 := fun p hp => by
  rw [orbitPoint_zero_apply hp.ne_zero, norm_one]

/-- The prime zeta function `P(w) = Σ_p p^{−w}`. -/
def primeZeta (w : ℂ) : ℂ := ∑' p : Nat.Primes, eulerVar w (orbitPoint 0) p

theorem differentiableOn_primeZeta : DifferentiableOn ℂ primeZeta {w : ℂ | 1 < w.re} := by
  intro w hw
  have hw' : 1 < w.re := hw
  set η : ℝ := (w.re - 1) / 2 with hη
  have hη0 : 0 < η := by rw [hη]; linarith
  set U : Set ℂ := {v | 1 + η < v.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ (fun v => ∑' p : Nat.Primes, eulerVar v (orbitPoint 0) p) U := by
    refine Complex.differentiableOn_tsum_of_summable_norm
      (summable_primes_rpow (r := -(1 + η)) (by linarith)) (fun p v _ => ?_) hUo fun p v hv => ?_
    · refine DifferentiableAt.differentiableWithinAt ?_
      unfold eulerVar powCoeff
      exact (DifferentiableAt.const_cpow (by fun_prop)
        (Or.inl (by exact_mod_cast p.2.ne_zero))).mul_const _
    · have hv' : 1 + η < v.re := hv
      rw [norm_eulerVar norm_orbitPoint_zero_prime p.2]
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast p.2.one_lt.le) (by linarith)
  exact (hd.differentiableAt (hUo.mem_nhds (by show 1 + η < w.re; rw [hη]; linarith))).differentiableWithinAt

/-- The logarithm of `ζ`: `exp(P(w) + h(w)) = ζ(w)` on `Re w > 1`. -/
theorem exp_primeZeta_add_hullRem {w : ℂ} (hw : 1 < w.re) :
    Complex.exp (primeZeta w + hullRem w (orbitPoint 0)) = riemannZeta w := by
  have h := exp_tsum_eq_tsum (f := orbitPoint 0) (norm_orbitPoint_le 0) norm_orbitPoint_zero_prime hw
  rw [tsum_orbitPoint hw] at h
  unfold primeZeta
  rw [h]
  simp

/-- `P' = ζ'/ζ − h'` on `Re w > 1`. -/
theorem deriv_primeZeta {w : ℂ} (hw : 1 < w.re) :
    deriv primeZeta w =
      deriv riemannZeta w / riemannZeta w - deriv (fun v => hullRem v (orbitPoint 0)) w := by
  have hU : IsOpen {v : ℂ | 1 < v.re} := isOpen_lt continuous_const Complex.continuous_re
  have hP : DifferentiableAt ℂ primeZeta w := differentiableOn_primeZeta.differentiableAt (hU.mem_nhds hw)
  have hh : DifferentiableAt ℂ (fun v => hullRem v (orbitPoint 0)) w :=
    (analyticOnNhd_hullRem norm_orbitPoint_zero_prime w (by show 1 / 2 < w.re; linarith)).differentiableAt
  have h1 : HasDerivAt (fun v => Complex.exp (primeZeta v + hullRem v (orbitPoint 0)))
      (Complex.exp (primeZeta w + hullRem w (orbitPoint 0)) *
        (deriv primeZeta w + deriv (fun v => hullRem v (orbitPoint 0)) w)) w :=
    (hP.hasDerivAt.add hh.hasDerivAt).cexp
  have h2 : riemannZeta =ᶠ[𝓝 w] fun v => Complex.exp (primeZeta v + hullRem v (orbitPoint 0)) := by
    filter_upwards [hU.mem_nhds hw] with v hv
    exact (exp_primeZeta_add_hullRem hv).symm
  have h3 : deriv riemannZeta w = riemannZeta w *
      (deriv primeZeta w + deriv (fun v => hullRem v (orbitPoint 0)) w) := by
    rw [h2.deriv_eq, h1.deriv, exp_primeZeta_add_hullRem hw]
  have hζ : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hw
  rw [h3, mul_div_cancel_left₀ _ hζ]
  ring

/-- **The prime zeta function is bounded on horizontal rays ending at `1 + iq`, `q ≠ 0`.** -/
theorem exists_bound_primeZeta {q : ℝ} (hq : q ≠ 0) :
    ∃ B : ℝ, ∀ σ : ℝ, 1 < σ → ‖primeZeta ⟨σ, q⟩‖ ≤ B := by
  set w₀ : ℂ := ⟨1, q⟩ with hw₀
  have hw₀1 : w₀ ≠ 1 := fun h => hq (by simpa [hw₀] using congrArg Complex.im h)
  have hζ0 : riemannZeta w₀ ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by simp [hw₀])
  have hζa : AnalyticAt ℂ riemannZeta w₀ := by
    have h : DifferentiableOn ℂ riemannZeta {w : ℂ | w ≠ 1} := fun w hw =>
      (differentiableAt_riemannZeta hw).differentiableWithinAt
    exact h.analyticAt (isOpen_ne.mem_nhds hw₀1)
  have hha : AnalyticAt ℂ (fun v => hullRem v (orbitPoint 0)) w₀ :=
    analyticOnNhd_hullRem norm_orbitPoint_zero_prime w₀ (by show 1 / 2 < w₀.re; simp [hw₀]; norm_num)
  set D : ℂ → ℂ := fun v => deriv riemannZeta v / riemannZeta v -
    deriv (fun v => hullRem v (orbitPoint 0)) v with hD
  have hDc : ContinuousAt D w₀ :=
    (hζa.deriv.continuousAt.div hζa.continuousAt hζ0).sub hha.deriv.continuousAt
  set K : ℝ := ‖D w₀‖ + 1 with hK
  have hK0 : 0 < K := by positivity
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff_ball.mp
    (hDc.norm.tendsto.eventually (gt_mem_nhds (lt_add_one ‖D w₀‖)))
  set V : Set ℂ := ball w₀ ρ ∩ {w : ℂ | 1 < w.re} with hV
  have hUo : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hVc : Convex ℝ V := (convex_ball _ _).inter (convex_halfSpace_re_gt _)
  have hderiv : ∀ w ∈ V, ‖deriv primeZeta w‖ ≤ K := fun w hw => by
    rw [deriv_primeZeta hw.2]
    exact (hball w hw.1).le
  have hmemV : ∀ σ : ℝ, 1 < σ → σ < 1 + ρ → (⟨σ, q⟩ : ℂ) ∈ V := fun σ h1 h2 => by
    refine ⟨?_, h1⟩
    rw [mem_ball, Complex.dist_of_im_eq (z := (⟨σ, q⟩ : ℂ)) (w := w₀) rfl, Real.dist_eq]
    show |σ - 1| < ρ
    rw [abs_of_pos (by linarith)]
    linarith
  set w₁ : ℂ := ⟨1 + ρ / 2, q⟩ with hw₁
  have hw₁V : w₁ ∈ V := hmemV _ (by linarith) (by linarith)
  set C₁ : ℝ := ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(1 + ρ / 2)) with hC₁
  have hC₁s : Summable fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-(1 + ρ / 2)) :=
    summable_primes_rpow (by linarith)
  refine ⟨max (‖primeZeta w₁‖ + K * ρ) C₁, fun σ hσ => ?_⟩
  by_cases hσρ : σ < 1 + ρ / 2
  · have hw := hmemV σ hσ (by linarith)
    have h1 := hVc.norm_image_sub_le_of_norm_deriv_le
      (fun z hz => differentiableOn_primeZeta.differentiableAt (hUo.mem_nhds hz.2)) hderiv hw₁V hw
    have h2 : ‖(⟨σ, q⟩ : ℂ) - w₁‖ ≤ ρ := by
      rw [← dist_eq_norm, Complex.dist_of_im_eq (z := (⟨σ, q⟩ : ℂ)) (w := w₁) rfl, Real.dist_eq]
      show |σ - (1 + ρ / 2)| ≤ ρ
      rw [abs_le]
      constructor <;> linarith
    have h3 : ‖primeZeta ⟨σ, q⟩‖ ≤ ‖primeZeta w₁‖ + ‖primeZeta ⟨σ, q⟩ - primeZeta w₁‖ := by
      have := norm_add_le (primeZeta w₁) (primeZeta ⟨σ, q⟩ - primeZeta w₁)
      rwa [add_sub_cancel] at this
    have h4 : K * ‖(⟨σ, q⟩ : ℂ) - w₁‖ ≤ K * ρ := mul_le_mul_of_nonneg_left h2 hK0.le
    exact (by linarith : ‖primeZeta ⟨σ, q⟩‖ ≤ ‖primeZeta w₁‖ + K * ρ).trans (le_max_left _ _)
  · refine le_trans ?_ (le_max_right _ _)
    refine tsum_of_norm_bounded hC₁s.hasSum fun p => ?_
    rw [norm_eulerVar norm_orbitPoint_zero_prime p.2]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast p.2.one_lt.le)
      (by show -σ ≤ -(1 + ρ / 2); linarith)

/-! ### The remainder over order-two points -/

/-- Over an order-two point the quadratic part of the logarithm is `½ P(2s)`. -/
theorem hullRem_sign_eq {ω : Omega} (hsign : ∀ p, p.Prime → X p ω = 1 ∨ X p ω = -1) {s : ℂ}
    (hs : 1 / 2 < s.re) :
    hullRem s (signHom ω) = primeZeta (2 * s) / 2 + ∑' p : Nat.Primes, cubicRem s (signHom ω) p := by
  have hu := norm_signHom_prime ω
  have h1 : hullRem s (signHom ω) = ∑' p : Nat.Primes, eulerVar s (signHom ω) p ^ 2 / 2 +
      ∑' p : Nat.Primes, cubicRem s (signHom ω) p := by
    rw [← Summable.tsum_add (summable_quad hu hs) (summable_cubicRem hu hs)]
    unfold hullRem cubicRem
    exact tsum_congr fun p => by ring
  rw [h1]
  congr 1
  unfold primeZeta
  rw [← tsum_div_const]
  refine tsum_congr fun p => ?_
  have hp0 : ((p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  have hX : signHom ω p ^ 2 = 1 := by
    rw [signHom_apply, if_neg p.2.ne_zero]
    rcases hsign p p.2 with h | h <;> rw [h] <;> norm_num
  unfold eulerVar powCoeff
  rw [orbitPoint_zero_apply p.2.ne_zero, mul_one, mul_pow, hX, mul_one, sq,
    ← Complex.cpow_add _ _ hp0]
  ring_nf

theorem two_mul_rayPoint (τ : ℝ) (j : ℕ) :
    2 * rayPoint τ j = ⟨1 + 2 / ((j : ℝ) + 1), 2 * τ⟩ := by
  apply Complex.ext
  · simp only [Complex.mul_re, rayPoint]
    norm_num
    ring
  · simp only [Complex.mul_im, rayPoint]
    norm_num

theorem measurable_hullRem_sign {s : ℂ} (hs : 1 / 2 < s.re) :
    Measurable fun ω : Omega => hullRem s (signHom ω) := by
  have hpart : ∀ ω : Omega, Tendsto (fun N : ℕ => ∑ p ∈ N.primesBelow, localRem s (signHom ω) p) atTop
      (𝓝 (hullRem s (signHom ω))) := fun ω =>
    tendsto_sum_primesBelow (g := fun p => localRem s (signHom ω) p) (summable_localRem (norm_signHom_prime ω) hs)
  refine measurable_of_tendsto_metrizable (fun N => ?_) (tendsto_pi_nhds.mpr hpart)
  refine Finset.measurable_sum _ fun p hp => ?_
  have hz : Measurable fun ω : Omega => eulerVar s (signHom ω) p := by
    unfold eulerVar
    have : (fun ω : Omega => powCoeff s p * signHom ω p) = fun ω => powCoeff s p * X p ω := by
      funext ω
      rw [signHom_apply, if_neg (Nat.mem_primesBelow.mp hp).2.ne_zero]
    rw [this]
    exact measurable_const.mul (measurable_X p)
  unfold localRem
  exact (Complex.measurable_log.comp (measurable_const.sub hz)).neg.sub hz

/-- The partial sums of the Steinhaus prime series are the prime sums of the lacunary family. -/
theorem dirichletPartialSum_primePhaseCoeff_eq (ω : Omega) (N : ℕ) (s : ℂ) :
    dirichletPartialSum (primePhaseCoeff ω) N s = primeSumOf (fun n ω => X n ω) (N + 1) s ω := by
  unfold dirichletPartialSum primeSumOf Nat.primesBelow
  rw [Finset.sum_filter, Finset.sum_range_succ', if_neg Nat.not_prime_zero, add_zero]
  refine Finset.sum_congr rfl fun n _ => ?_
  unfold primePhaseCoeff powCoeff
  by_cases hp : (n + 1).Prime
  · rw [if_pos hp, if_pos hp]
    push_cast
    ring
  · rw [if_neg hp, if_neg hp, zero_mul]

/-- **Rays are unbounded.** For almost every order-two point, the logarithm of the fibre is unbounded along every horizontal ray ending at a nonzero rational point of the line. -/
theorem ae_sign_ray_unbounded :
    ∀ᵐ ω ∂signMeasure, ∀ q : ℚ, q ≠ 0 → ∀ M J : ℕ, ¬ ∀ j, J ≤ j →
      ‖dirichletSum (primePhaseCoeff ω) (rayPoint q j) + hullRem (rayPoint q j) (signHom ω)‖ ≤ M := by
  simp only [ae_all_iff]
  intro q hq M J
  have hq2 : 2 * (q : ℝ) ≠ 0 := by
    have : (q : ℝ) ≠ 0 := by exact_mod_cast hq
    positivity
  obtain ⟨B, hB⟩ := exists_bound_primeZeta hq2
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 2 (by norm_num))
  set c : ℝ := ∑' p : Nat.Primes, 2 * ((p : ℕ) : ℝ) ^ (-(3 / 2) : ℝ) with hc
  have hsc : Summable fun p : Nat.Primes => 2 * ((p : ℕ) : ℝ) ^ (-(3 / 2) : ℝ) :=
    (summable_primes_rpow (by norm_num)).mul_left 2
  have hc0 : 0 ≤ c := tsum_nonneg fun p => by positivity
  -- The remainder is bounded on the rays.
  have hrem : ∀ j, ∀ᵐ ω ∂signMeasure, ‖hullRem (rayPoint q j) (signHom ω)‖ ≤ B / 2 + c := by
    intro j
    filter_upwards [ae_X_prime_sign] with ω hω
    have hs := half_lt_rayPoint_re (q : ℝ) j
    rw [hullRem_sign_eq hω hs]
    have h1 : ‖primeZeta (2 * rayPoint q j)‖ ≤ B := by
      rw [two_mul_rayPoint]
      exact hB _ (by have : (0 : ℝ) < 2 / ((j : ℝ) + 1) := by positivity
                     linarith)
    have h2 : ‖∑' p : Nat.Primes, cubicRem (rayPoint q j) (signHom ω) p‖ ≤ c :=
      tsum_of_norm_bounded hsc.hasSum fun p => norm_cubicRem_le (norm_signHom_prime ω) p.2 hs
    refine (norm_add_le _ _).trans ?_
    rw [norm_div, Complex.norm_two]
    linarith
  rw [ae_iff]
  simp only [not_not]
  refine isLacunary_sign.measure_bounded_primeSumOf_eq_zero (s := rayPoint q)
    (fun j => half_lt_rayPoint_re _ j) ?_ (g := fun j ω => dirichletSum (primePhaseCoeff ω) (rayPoint q j))
    (e := fun j ω => hullRem (rayPoint q j) (signHom ω)) (fun j => ?_)
    (fun j => (measurable_hullRem_sign (half_lt_rayPoint_re _ j)).aemeasurable)
    (C := (B / 2 + c) ^ 2) (by positivity) (fun j => ?_) (M : ℝ) J
  · have h1 : Tendsto (fun j : ℕ => (1 / 2 : ℝ) + 1 / ((j : ℝ) + 1)) atTop (𝓝 (1 / 2 + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
    rw [add_zero] at h1
    exact h1
  · filter_upwards [ae_mem_primeHolomorphicEvent] with ω hω
    have hk : (((1 / 2 + 1 / (((j + 1 : ℕ) : ℝ) + 1) : ℝ) : ℂ)).re < (rayPoint q j).re := by
      show 1 / 2 + 1 / (((j + 1 : ℕ) : ℝ) + 1) < 1 / 2 + 1 / ((j : ℝ) + 1)
      have : (1 : ℝ) / (((j + 1 : ℕ) : ℝ) + 1) < 1 / ((j : ℝ) + 1) := by
        push_cast
        exact one_div_lt_one_div_of_lt (by positivity) (by linarith)
      linarith
    have hconv := convergesAt_primePhaseCoeff (Set.mem_iInter.mp hω (j + 1))
    have ht := (tendstoLocallyUniformlyOn_dirichletPartialSum hconv).tendsto_at hk
    have ht' : Tendsto (fun N => primeSumOf (fun n ω => X n ω) (N + 1) (rayPoint q j) ω) atTop
        (𝓝 (dirichletSum (primePhaseCoeff ω) (rayPoint q j))) :=
      ht.congr fun N => dirichletPartialSum_primePhaseCoeff_eq ω N _
    exact (tendsto_add_atTop_iff_nat 1).mp ht'
  · calc ∫⁻ ω, ENNReal.ofReal (‖hullRem (rayPoint q j) (signHom ω)‖ ^ 2) ∂signMeasure
        ≤ ∫⁻ _ω, ENNReal.ofReal ((B / 2 + c) ^ 2) ∂signMeasure := by
          refine lintegral_mono_ae ?_
          filter_upwards [hrem j] with ω hω
          exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) hω 2)
      _ = ENNReal.ofReal ((B / 2 + c) ^ 2) := by
          rw [lintegral_const, measure_univ, mul_one]

/-! ### The boundary -/

/-- **The natural boundary over order-two points.** For almost every order-two point, the fibre extends to a zero-free analytic function on `Re s > ½`, with no analytic continuation across any point of `Re s = ½`. -/
theorem ae_sign_natural_boundary :
    ∀ᵐ ω ∂signMeasure, (∀ p, p.Prime → X p ω = 1 ∨ X p ω = -1) ∧
      ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F rightHalf ∧
        (∀ s, 1 < s.re → F s = ∑' n, signHom ω n * (n : ℂ) ^ (-s)) ∧ (∀ s ∈ rightHalf, F s ≠ 0) ∧
        ∀ (τ₀ r : ℝ) (H : ℂ → ℂ), 0 < r → AnalyticOnNhd ℂ H (ball (⟨1 / 2, τ₀⟩ : ℂ) r) →
          ¬ ∀ s ∈ ball (⟨1 / 2, τ₀⟩ : ℂ) r, s ∈ rightHalf → H s = F s := by
  filter_upwards [ae_X_prime_sign, ae_mem_primeHolomorphicEvent, ae_sign_ray_unbounded]
    with ω hsign hω hray
  have hU : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hP : AnalyticOnNhd ℂ (dirichletSum (primePhaseCoeff ω)) rightHalf :=
    (differentiableOn_dirichletSum_primePhaseCoeff hω).analyticOnNhd hU
  set W : ℂ → ℂ := fun s => dirichletSum (primePhaseCoeff ω) s + hullRem s (signHom ω) with hW
  have hWa : AnalyticOnNhd ℂ W rightHalf := hP.add (analyticOnNhd_hullRem (norm_signHom_prime ω))
  refine ⟨hsign, fun s => Complex.exp (W s), fun s hs => (hWa s hs).cexp, fun s hs => ?_,
    fun s _ => Complex.exp_ne_zero _, fun τ₀ r H hr hH => no_continuation_of_rays hWa hray hr hH⟩
  have h1 : dirichletSum (primePhaseCoeff ω) s = ∑' p : Nat.Primes, eulerVar s (signHom ω) p := by
    rw [← (hasSum_primePhase_dirichletSum (ω := ω) hs).tsum_eq]
    refine tsum_congr fun p => ?_
    unfold eulerVar powCoeff
    rw [signHom_apply, if_neg p.2.ne_zero, mul_comm]
  simp only [hW]
  rw [h1]
  exact exp_tsum_eq_tsum (norm_signHom_le ω) (norm_signHom_prime ω) hs

end

end GaloisForLFunctions.PrimeTorusTheory
