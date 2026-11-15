import GaloisForLFunctions.TensorPowerProgramme.APolarizedBaseWhoseAdamsSquaresContinueIsPure
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.OneCycleReadsTheWidthAtEveryPrime

/-!
# The axioms of a pencil through ζ

The missing object N1 of the tensor-power route, as a list of axioms (`PencilThroughZeta`): a base
of points `x` with frequencies `ℓ(x) = log N(x) ≥ 0` and weights `λ(x) ≥ 0`, real level traces
`t(x, n)` (the trace of the `n`-th power of Frobenius at `x`), and

* **the Deligne pole law**: for every `k ≥ 1` the `2k`-th tensor moment
  `Σ_{x,n} λ(x) t(x, n)^{2k} N(x)^{−ns}` converges somewhere and continues analytically to
  `Re s > 1`: the first pole is fixed in advance, whatever the parameters are;
* **`ζ` as a fibre**: at one point `x₀` of positive weight, of norm a prime `p`, the level traces
  have the size of the Lefschetz numbers `W(T_{p^n} g, g)` of `ζ` for the one cycle `g` that
  reads the zero width at every prime (`zetaCycle`).

* **A pencil proves RH** (`riemannHypothesis_of_pencil`). Landau's theorem turns the continuation
  into convergence on `Re s > 1`; the levels of `x₀` alone then bound the Lefschetz numbers by
  `C p^{n/k}`, and the one-cycle law gives `p^w ≤ p^{1/k}` for every `k`.
* **A pencil exists iff RH** (`riemannHypothesis_iff_nonempty_pencil`). Under RH the one-point
  base `{p = 2}` is a pencil: its Lefschetz numbers are bounded. The axiom list carries no
  information beyond RH unless the pole law has a source independent of the parameters.

So the specification of N1 is not the list itself but the origin of the pole law. The corpus has
three sources and their verdicts: flow data and abelian bases, where the constituents are the
shifted modes and the pole law is the conclusion (`summable_flowMomentTerm_iff`,
`summable_twistMomentTerm_iff`); and polarized bases whose Adams powers continue to `Re s > 1`
(`norm_eq_one_of_adams_continue`), where the constituents are `L`-functions of other objects. A
pencil through `ζ` is a polarized base of the third kind with `ζ` as a fibre.
-/

open Complex Filter Topology
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open GaloisForLFunctions.SquareRootThreshold (zetaZeroWidth)

noncomputable section

namespace GaloisForLFunctions.TensorPowerProgramme

/-- The one cycle of `ζ` that reads the zero width at every prime. -/
def zetaCycle : ℝ → ℂ := Classical.choose zeta_exists_universal_lefschetz_growth

theorem zetaCycle_growth {p : ℕ} (hp : p.Prime) {R : ℝ} (hR : 1 ≤ R) :
    (∃ C, ∀ k : ℕ, ‖towerMoment Zeta23.zetaZeroConfig zetaCycle (Real.log p) k‖ ≤ C * R ^ k) ↔
      (p : ℝ) ^ zetaZeroWidth ≤ R :=
  (Classical.choose_spec zeta_exists_universal_lefschetz_growth).2.2 p hp R hR

/-- **A pencil through `ζ`** (the object N1 of the tensor-power route). -/
structure PencilThroughZeta (ι : Type) where
  /-- frequencies `log N(x)` -/
  ℓ : ι → ℝ
  /-- weights of the points -/
  lam : ι → ℝ
  /-- real trace of the `n`-th power of Frobenius at `x` -/
  trace : ι → ℕ → ℝ
  ℓ_nonneg : ∀ x, 0 ≤ ℓ x
  lam_nonneg : ∀ x, 0 ≤ lam x
  /-- the Deligne pole law for every even tensor power -/
  poleLaw : ∀ k : ℕ, 1 ≤ k → ∃ σ₁ : ℝ,
    Summable (gdTwistTerm (fun q : ι × ℕ => lam q.1 * trace q.1 (q.2 + 1) ^ (2 * k))
      (levelFreq ℓ) σ₁ 0) ∧
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s | 1 < s.re} ∧ ∀ s : ℂ, σ₁ < s.re →
      G s = gdSeries (fun q : ι × ℕ => lam q.1 * trace q.1 (q.2 + 1) ^ (2 * k)) (levelFreq ℓ) s
  /-- the point carrying `ζ` -/
  x₀ : ι
  /-- its norm, a prime -/
  p : ℕ
  prime : p.Prime
  freq_x₀ : ℓ x₀ = Real.log p
  weight_x₀ : 0 < lam x₀
  /-- the level traces at `x₀` have the size of the Lefschetz numbers of `ζ` at `p` -/
  zeta_fibre : ∀ n : ℕ,
    |trace x₀ n| = ‖towerMoment Zeta23.zetaZeroConfig zetaCycle (Real.log p) n‖

variable {ι : Type}

theorem pencil_coeff_nonneg (P : PencilThroughZeta ι) (k : ℕ) (q : ι × ℕ) :
    0 ≤ P.lam q.1 * P.trace q.1 (q.2 + 1) ^ (2 * k) :=
  mul_nonneg (P.lam_nonneg _) (by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _)

/-- Under the pole law the `2k`-th tensor moment converges at `σ = 2`. -/
theorem summable_pencil_two (P : PencilThroughZeta ι) {k : ℕ} (hk : 1 ≤ k) :
    Summable (gdTwistTerm (fun q : ι × ℕ => P.lam q.1 * P.trace q.1 (q.2 + 1) ^ (2 * k))
      (levelFreq P.ℓ) 2 0) := by
  obtain ⟨σ₁, hsum, G, hG, hagree⟩ := P.poleLaw k hk
  have ha := pencil_coeff_nonneg P k
  have hf := levelFreq_nonneg P.ℓ_nonneg
  rcases le_or_gt σ₁ 2 with hle | hlt
  · exact summable_gdTwistTerm_of_le ha hf hsum hle
  · exact general_landau_summable_of_halfPlane_analytic ha hf hsum (by linarith : (1 : ℝ) < σ₁)
      hG hagree (by norm_num : (1 : ℝ) < 2)

/-- **The `k`-th tensor power bounds the width by `1/k`.** -/
theorem zetaZeroWidth_le_of_pencil (P : PencilThroughZeta ι) {k : ℕ} (hk : 1 ≤ k) :
    zetaZeroWidth ≤ 1 / k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hp1 : (1 : ℝ) < P.p := by exact_mod_cast P.prime.one_lt
  have hp0 : (0 : ℝ) < P.p := by linarith
  have ha := pencil_coeff_nonneg P k
  have hf := levelFreq_nonneg P.ℓ_nonneg
  have hx : Summable fun n : ℕ => gdTwistTerm
      (fun q : ι × ℕ => P.lam q.1 * P.trace q.1 (q.2 + 1) ^ (2 * k)) (levelFreq P.ℓ) 2 0 (P.x₀, n) :=
    (summable_pencil_two P hk).comp_injective
      (fun a b h => (Prod.mk.inj h).2 : Function.Injective fun n : ℕ => (P.x₀, n))
  set C := ∑' n : ℕ, gdTwistTerm (fun q : ι × ℕ => P.lam q.1 * P.trace q.1 (q.2 + 1) ^ (2 * k))
    (levelFreq P.ℓ) 2 0 (P.x₀, n)
  have hC0 : 0 ≤ C := tsum_nonneg fun n => gdTwistTerm_nonneg ha hf 2 0 _
  -- the rate ρ = p^{1/k}
  set ρ : ℝ := (P.p : ℝ) ^ (1 / (k : ℝ))
  have hρ1 : 1 ≤ ρ := Real.one_le_rpow hp1.le (by positivity)
  have hkne : (k : ℝ) ≠ 0 := hk0.ne'
  have hρk : ρ ^ (2 * k) = (P.p : ℝ) ^ 2 := by
    have h12 : (1 / (k : ℝ)) * ((2 * k : ℕ) : ℝ) = ((2 : ℕ) : ℝ) := by push_cast; field_simp
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le, h12, Real.rpow_natCast]
  set B : ℝ := (C / P.lam P.x₀) ^ (1 / (2 * k : ℝ))
  have hB0 : 0 ≤ B := Real.rpow_nonneg (div_nonneg hC0 (P.weight_x₀.le)) _
  have hB2k : B ^ (2 * k) = C / P.lam P.x₀ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (div_nonneg hC0 P.weight_x₀.le)]
    have : (1 / (2 * k : ℝ)) * ((2 * k : ℕ) : ℝ) = 1 := by push_cast; field_simp
    rw [this, Real.rpow_one]
  -- every level of x₀ is at most B ρ^{n+1}
  have hlev : ∀ n : ℕ, |P.trace P.x₀ (n + 1)| ≤ B * ρ ^ (n + 1) := by
    intro n
    have ht : gdTwistTerm (fun q : ι × ℕ => P.lam q.1 * P.trace q.1 (q.2 + 1) ^ (2 * k))
        (levelFreq P.ℓ) 2 0 (P.x₀, n) ≤ C := hx.le_tsum n fun j _ => gdTwistTerm_nonneg ha hf 2 0 _
    simp only [gdTwistTerm, pow_zero, mul_one] at ht
    have hE := exp_levelFreq P.ℓ P.x₀ n
    rw [P.freq_x₀, Real.exp_log hp0] at hE
    have h1 : P.trace P.x₀ (n + 1) ^ (2 * k) ≤ (C / P.lam P.x₀) * ((P.p : ℝ) ^ (n + 1)) ^ 2 := by
      have h3 := mul_le_mul_of_nonneg_right ht (sq_nonneg ((P.p : ℝ) ^ (n + 1)))
      have h5 : P.lam P.x₀ * P.trace P.x₀ (n + 1) ^ (2 * k) *
          Real.exp (-(2 * levelFreq P.ℓ (P.x₀, n))) * ((P.p : ℝ) ^ (n + 1)) ^ 2 =
          P.lam P.x₀ * P.trace P.x₀ (n + 1) ^ (2 * k) := by
        rw [mul_assoc (P.lam P.x₀ * P.trace P.x₀ (n + 1) ^ (2 * k)), hE, mul_one]
      rw [div_mul_eq_mul_div, le_div_iff₀ P.weight_x₀]
      linarith
    have h2 : |P.trace P.x₀ (n + 1)| ^ (2 * k) ≤ (B * ρ ^ (n + 1)) ^ (2 * k) := by
      have hev : |P.trace P.x₀ (n + 1)| ^ (2 * k) = P.trace P.x₀ (n + 1) ^ (2 * k) := by
        rw [pow_mul, pow_mul, sq_abs]
      have hR : (B * ρ ^ (n + 1)) ^ (2 * k) = (C / P.lam P.x₀) * ((P.p : ℝ) ^ (n + 1)) ^ 2 := by
        rw [mul_pow, ← pow_mul, mul_comm (n + 1) (2 * k), pow_mul ρ (2 * k) (n + 1), hρk, hB2k]
        ring
      rw [hev, hR]
      exact h1
    exact (pow_le_pow_iff_left₀ (abs_nonneg _) (by positivity) (by omega)).mp h2
  -- the Lefschetz numbers of ζ at p grow at most like ρ^n
  have hgrow : ∃ D, ∀ n : ℕ,
      ‖towerMoment Zeta23.zetaZeroConfig zetaCycle (Real.log P.p) n‖ ≤ D * ρ ^ n := by
    refine ⟨max B |P.trace P.x₀ 0|, fun n => ?_⟩
    rw [← P.zeta_fibre n]
    rcases n with _ | n
    · rw [pow_zero, mul_one]
      exact le_max_right _ _
    · calc |P.trace P.x₀ (n + 1)| ≤ B * ρ ^ (n + 1) := hlev n
        _ ≤ max B |P.trace P.x₀ 0| * ρ ^ (n + 1) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  have hw := (zetaCycle_growth P.prime hρ1).mp hgrow
  rwa [Real.rpow_le_rpow_left_iff hp1] at hw

/-- **A pencil through `ζ` proves RH.** -/
theorem riemannHypothesis_of_pencil (P : PencilThroughZeta ι) : RiemannHypothesis := by
  rw [SquareRootThreshold.riemannHypothesis_iff_zetaZeroWidth_eq_zero]
  refine le_antisymm ?_ SquareRootThreshold.zetaZeroWidth_nonneg
  by_contra hpos
  push Not at hpos
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / zetaZeroWidth)
  have hk1 : 1 ≤ k := by
    have : (0 : ℝ) < k := lt_trans (by positivity) hk
    exact_mod_cast this
  have h := zetaZeroWidth_le_of_pencil P hk1
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
  rw [div_lt_iff₀ hpos] at hk
  rw [le_div_iff₀ hk0] at h
  linarith

/-- Under RH the Lefschetz numbers of `ζ` at a prime are bounded. -/
theorem exists_bound_towerMoment_of_riemannHypothesis (hRH : RiemannHypothesis) {p : ℕ}
    (hp : p.Prime) :
    ∃ C, ∀ k : ℕ, ‖towerMoment Zeta23.zetaZeroConfig zetaCycle (Real.log p) k‖ ≤ C := by
  have hw : zetaZeroWidth = 0 :=
    SquareRootThreshold.riemannHypothesis_iff_zetaZeroWidth_eq_zero.mp hRH
  obtain ⟨C, hC⟩ := (zetaCycle_growth hp le_rfl).mpr (by rw [hw, Real.rpow_zero])
  exact ⟨C, fun k => by simpa using hC k⟩

/-- **A pencil exists iff RH.** Under RH the single point `p = 2`, with the Lefschetz numbers of
`ζ` as its level traces, is a pencil: its tensor moments converge on `Re s > 0`. -/
theorem riemannHypothesis_iff_nonempty_pencil :
    RiemannHypothesis ↔ Nonempty (PencilThroughZeta Unit) := by
  refine ⟨fun hRH => ?_, fun ⟨P⟩ => riemannHypothesis_of_pencil P⟩
  obtain ⟨C, hC⟩ := exists_bound_towerMoment_of_riemannHypothesis hRH Nat.prime_two
  set L : ℝ := Real.log ((2 : ℕ) : ℝ)
  set t : ℕ → ℝ := fun n => ‖towerMoment Zeta23.zetaZeroConfig zetaCycle L n‖
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hlog2 : 0 < L := Real.log_pos (by norm_num)
  have hf : ∀ q : Unit × ℕ, 0 ≤ levelFreq (fun _ : Unit => L) q :=
    levelFreq_nonneg fun _ => hlog2.le
  refine ⟨⟨fun _ => L, fun _ => 1, fun _ n => t n, fun _ => hlog2.le, fun _ => zero_le_one,
    fun k _ => ?_, (), 2, Nat.prime_two, rfl, one_pos, fun n => abs_of_nonneg (norm_nonneg _)⟩⟩
  have ha : ∀ q : Unit × ℕ, 0 ≤ (1 : ℝ) * t (q.2 + 1) ^ (2 * k) := fun q => by
    rw [one_mul, pow_mul]; exact pow_nonneg (sq_nonneg _) _
  -- the coefficients are at most C^{2k}, so the series converges on Re s > 0
  have hsum : ∀ σ : ℝ, 0 < σ → Summable (gdTwistTerm (fun q : Unit × ℕ => (1 : ℝ) * t (q.2 + 1) ^ (2 * k))
      (levelFreq fun _ => L) σ 0) := by
    intro σ hσ
    set r := Real.exp (-(σ * L))
    have hr0 : 0 ≤ r := (Real.exp_pos _).le
    have hr1 : r < 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by nlinarith)
    have hg : Summable fun n : ℕ => C ^ (2 * k) * r ^ (n + 1) :=
      ((summable_geometric_of_lt_one hr0 hr1).mul_left r).mul_left (C ^ (2 * k)) |>.congr
        fun n => by ring
    have hg' : Summable fun q : Unit × ℕ => C ^ (2 * k) * r ^ (q.2 + 1) :=
      (Equiv.summable_iff (Equiv.punitProd ℕ)).mpr hg
    refine Summable.of_nonneg_of_le (gdTwistTerm_nonneg ha hf σ 0) (fun q => ?_) hg'
    have hexp : Real.exp (-(σ * levelFreq (fun _ : Unit => L) q)) = r ^ (q.2 + 1) := by
      rw [← Real.exp_nat_mul]
      congr 1
      simp only [levelFreq]
      push_cast
      ring
    have ht : t (q.2 + 1) ^ (2 * k) ≤ C ^ (2 * k) :=
      pow_le_pow_left₀ (norm_nonneg _) (hC _) _
    simp only [gdTwistTerm, pow_zero, mul_one, one_mul, hexp]
    exact mul_le_mul_of_nonneg_right ht (pow_nonneg hr0 _)
  refine ⟨2, hsum 2 two_pos, gdSeries _ _, fun s hs => ?_, fun s _ => rfl⟩
  have hs1 : (1 : ℝ) < s.re := hs
  exact (RHTower.differentiableAt_gdSeries ha hf (hsum 1 one_pos) hs1).differentiableWithinAt

end GaloisForLFunctions.TensorPowerProgramme
