import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheVonMangoldtSquareIsTheZetaSource
import GaloisForLFunctions.RHTower.DirichletLogDerivation

/-!
# The renormalized square is Selberg's source

The Rankin–Selberg square `(ζ′/ζ)² = L(Λ ⋆ Λ)` carries, at a zero of order `m`, the self-term
`m²/(s − ρ)²` and the residue `2m R(ρ)`, where `R` is the regular part of `ζ′/ζ` — the field of the
other zeros. The self-term is the diagonal of the electrostatic interaction, the residue its
content. This file renormalizes the diagonal by the **degree** and identifies the result.

* **The counterterm identity** (`deriv_deriv_div_eq`): `F″/F = (F′/F)² + (F′/F)′`. The counterterm
  `(F′/F)′` has double pole `−m` and no residue.
* **Self-terms at a zero** (`selfTerm_and_residue_of_analyticOrderAt`): for `F` analytic at a zero
  of order `m`, the double-pole coefficient of `(F′/F)²` is `m²` and that of `F″/F` is `m(m − 1)`;
  both residues are `2m R(ρ)`. Renormalization lowers the self-term from `m²` to `m(m − 1)`, which
  vanishes exactly at simple zeros, and leaves the field untouched.
* **Selberg's source** (`selbergSource`, `selbergSource_eq`, `selbergSource_nonneg`,
  `selbergSource_prime_pow`): on the arithmetic side the counterterm is `Λ(n) log n` — the von
  Mangoldt weight times the degree `log n` of the Hecke correspondence `T_n` — and the renormalized
  source `Λ₂ = Λ log + Λ ⋆ Λ = μ ⋆ log²` is nonnegative, with `Λ₂(p^k) = (2k − 1)(log p)²`.
* **Its Dirichlet series** (`LSeries_selbergSource`): `L(Λ₂, s) = ζ″(s)/ζ(s)` for `Re s > 1`.

So the double pole of `Λ ⋆ Λ` has a positivity-preserving, degree-defined renormalization whose
residue at every simple zero is twice the field: the zero-side half of an arithmetic adjunction.
-/

open Filter ArithmeticFunction Set
open scoped Topology

namespace GaloisForLFunctions.ArithmeticElectrostatics

noncomputable section

/-! ### The counterterm identity -/

/-- **The counterterm identity** `F″/F = (F′/F)² + (F′/F)′`. -/
theorem deriv_deriv_div_eq {F : ℂ → ℂ} {s : ℂ} (hF : DifferentiableAt ℂ F s)
    (hF' : DifferentiableAt ℂ (deriv F) s) (hs : F s ≠ 0) :
    deriv (deriv F) s / F s = logDeriv F s ^ 2 + deriv (logDeriv F) s := by
  have h : deriv (logDeriv F) s =
      (deriv (deriv F) s * F s - deriv F s * deriv F s) / F s ^ 2 := by
    have : logDeriv F = fun z => deriv F z / F z := rfl
    rw [this]
    exact deriv_div hF' hF hs
  rw [h, logDeriv_apply]
  field_simp
  ring

/-- The derivative of the polar part `m/(z − ρ)`. -/
theorem hasDerivAt_polar (m ρ : ℂ) {z : ℂ} (hz : z ≠ ρ) :
    HasDerivAt (fun w => m / (w - ρ)) (-m / (z - ρ) ^ 2) z := by
  have h := (hasDerivAt_const z m).div ((hasDerivAt_id' z).sub_const ρ) (sub_ne_zero.mpr hz)
  convert h using 1
  ring

/-! ### Self-terms at a zero -/

/-- **Self-terms and residues at a zero of order `m`.** If `F` is analytic at a zero `ρ` of order
`m`, the regular part `R` of `F′/F` is analytic at `ρ`, and on a punctured neighbourhood

* `(z − ρ)² (F′/F)² → m²` and `(z − ρ)((F′/F)² − m²/(z − ρ)²) → 2m R(ρ)`;
* `(z − ρ)² F″/F → m(m − 1)` and `(z − ρ)(F″/F − m(m − 1)/(z − ρ)²) → 2m R(ρ)`. -/
theorem selfTerm_and_residue_of_analyticOrderAt {F : ℂ → ℂ} {ρ : ℂ} {m : ℕ}
    (hF : AnalyticAt ℂ F ρ) (hm : analyticOrderAt F ρ = m) :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R ρ ∧
      (∀ᶠ z in 𝓝[≠] ρ, logDeriv F z = m / (z - ρ) + R z) ∧
      Tendsto (fun z => (z - ρ) ^ 2 * logDeriv F z ^ 2) (𝓝[≠] ρ) (𝓝 ((m : ℂ) ^ 2)) ∧
      Tendsto (fun z => (z - ρ) * (logDeriv F z ^ 2 - (m : ℂ) ^ 2 / (z - ρ) ^ 2)) (𝓝[≠] ρ)
        (𝓝 (2 * m * R ρ)) ∧
      Tendsto (fun z => (z - ρ) ^ 2 * (deriv (deriv F) z / F z)) (𝓝[≠] ρ)
        (𝓝 ((m : ℂ) * (m - 1))) ∧
      Tendsto (fun z => (z - ρ) * (deriv (deriv F) z / F z - (m : ℂ) * (m - 1) / (z - ρ) ^ 2))
        (𝓝[≠] ρ) (𝓝 (2 * m * R ρ)) := by
  obtain ⟨g, hg, hgρ, hFg⟩ := (hF.analyticOrderAt_eq_natCast).mp hm
  -- an open neighbourhood on which `F = (z − ρ)^m g`, `F` and `g` are analytic and `g ≠ 0`
  have hev : ∀ᶠ z in 𝓝 ρ, F z = (z - ρ) ^ m * g z ∧ AnalyticAt ℂ F z ∧ AnalyticAt ℂ g z ∧
      g z ≠ 0 := by
    filter_upwards [hFg, hF.eventually_analyticAt, hg.eventually_analyticAt,
      hg.continuousAt.eventually_ne hgρ] with z h1 h2 h3 h4
    exact ⟨by simpa using h1, h2, h3, h4⟩
  obtain ⟨V, hVsub, hVopen, hρV⟩ := mem_nhds_iff.mp hev
  set R : ℂ → ℂ := logDeriv g
  have hRan : AnalyticAt ℂ R ρ := hg.deriv.div hg hgρ
  -- the logarithmic derivative on the punctured neighbourhood
  have hlog : ∀ z ∈ V, z ≠ ρ → logDeriv F z = m / (z - ρ) + R z := by
    intro z hz hzρ
    have hFz : F =ᶠ[𝓝 z] fun w => (w - ρ) ^ m * g w :=
      Filter.eventually_of_mem (hVopen.mem_nhds hz) fun w hw => (hVsub hw).1
    have hgz := (hVsub hz).2.2
    rw [logDeriv_apply, hFz.deriv_eq, (hVsub hz).1, ← logDeriv_apply,
      logDeriv_mul (f := fun w => (w - ρ) ^ m) (g := g) z (pow_ne_zero _ (sub_ne_zero.mpr hzρ)) hgz.2
        ((differentiableAt_id.sub_const ρ).pow m) hgz.1.differentiableAt,
      logDeriv_fun_pow (differentiableAt_id.sub_const ρ) m]
    simp only [R, logDeriv_apply, deriv_sub_const, deriv_id'']
    ring
  -- the renormalized square on the punctured neighbourhood
  have hsecond : ∀ z ∈ V, z ≠ ρ → deriv (deriv F) z / F z =
      (m : ℂ) * (m - 1) / (z - ρ) ^ 2 + 2 * m * R z / (z - ρ) + R z ^ 2 + deriv R z := by
    intro z hz hzρ
    have hFan := (hVsub hz).2.1
    have hgz := (hVsub hz).2.2
    have hFz0 : F z ≠ 0 := by
      rw [(hVsub hz).1]; exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hzρ)) hgz.2
    have hRz : DifferentiableAt ℂ R z := (hgz.1.deriv.div hgz.1 hgz.2).differentiableAt
    have hloc : logDeriv F =ᶠ[𝓝 z] fun w => m / (w - ρ) + R w := by
      filter_upwards [(hVopen.inter isOpen_ne).mem_nhds ⟨hz, hzρ⟩] with w hw
      exact hlog w hw.1 hw.2
    rw [deriv_deriv_div_eq hFan.differentiableAt hFan.deriv.differentiableAt hFz0, hloc.deriv_eq,
      ((hasDerivAt_polar (m : ℂ) ρ hzρ).add hRz.hasDerivAt).deriv, hlog z hz hzρ]
    have hd : z - ρ ≠ 0 := sub_ne_zero.mpr hzρ
    field_simp
    ring
  have hV : ∀ᶠ z in 𝓝[≠] ρ, z ∈ V ∧ z ≠ ρ :=
    (eventually_nhdsWithin_iff.mpr (Filter.eventually_of_mem (hVopen.mem_nhds hρV)
      fun z hz hzρ => ⟨hz, hzρ⟩))
  have hRc : Tendsto R (𝓝[≠] ρ) (𝓝 (R ρ)) := hRan.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hR'c : Tendsto (deriv R) (𝓝[≠] ρ) (𝓝 (deriv R ρ)) :=
    hRan.deriv.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hu : Tendsto (fun z => z - ρ) (𝓝[≠] ρ) (𝓝 0) := by
    have : Tendsto (fun z : ℂ => z - ρ) (𝓝 ρ) (𝓝 (ρ - ρ)) := tendsto_id.sub_const ρ
    rw [sub_self] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine ⟨R, hRan, hV.mono fun z hz => hlog z hz.1 hz.2, ?_, ?_, ?_, ?_⟩
  · have hlim : Tendsto (fun z => ((m : ℂ) + (z - ρ) * R z) ^ 2) (𝓝[≠] ρ) (𝓝 ((m : ℂ) ^ 2)) := by
      have := ((tendsto_const_nhds (x := (m : ℂ))).add (hu.mul hRc)).pow 2
      simpa using this
    refine hlim.congr' (hV.mono fun z hz => ?_)
    have hd : z - ρ ≠ 0 := sub_ne_zero.mpr hz.2
    rw [hlog z hz.1 hz.2]
    field_simp
  · have hlim : Tendsto (fun z => 2 * m * R z + (z - ρ) * R z ^ 2) (𝓝[≠] ρ)
        (𝓝 (2 * m * R ρ)) := by
      have := (hRc.const_mul (2 * (m : ℂ))).add (hu.mul (hRc.pow 2))
      simpa using this
    refine hlim.congr' (hV.mono fun z hz => ?_)
    have hd : z - ρ ≠ 0 := sub_ne_zero.mpr hz.2
    rw [hlog z hz.1 hz.2]
    field_simp
    ring
  · have hlim : Tendsto (fun z => (m : ℂ) * (m - 1) + (z - ρ) * (2 * m * R z) +
        (z - ρ) ^ 2 * (R z ^ 2 + deriv R z)) (𝓝[≠] ρ) (𝓝 ((m : ℂ) * (m - 1))) := by
      have := ((tendsto_const_nhds (x := (m : ℂ) * (m - 1))).add
        (hu.mul (hRc.const_mul (2 * (m : ℂ))))).add ((hu.pow 2).mul ((hRc.pow 2).add hR'c))
      simpa using this
    refine hlim.congr' (hV.mono fun z hz => ?_)
    have hd : z - ρ ≠ 0 := sub_ne_zero.mpr hz.2
    rw [hsecond z hz.1 hz.2]
    field_simp
    ring
  · have hlim : Tendsto (fun z => 2 * m * R z + (z - ρ) * (R z ^ 2 + deriv R z)) (𝓝[≠] ρ)
        (𝓝 (2 * m * R ρ)) := by
      have := (hRc.const_mul (2 * (m : ℂ))).add (hu.mul ((hRc.pow 2).add hR'c))
      simpa using this
    refine hlim.congr' (hV.mono fun z hz => ?_)
    have hd : z - ρ ≠ 0 := sub_ne_zero.mpr hz.2
    rw [hsecond z hz.1 hz.2]
    field_simp
    ring

/-! ### Selberg's source -/

/-- **Selberg's source** `Λ₂ = Λ·log + Λ ⋆ Λ`: the Rankin–Selberg square renormalized by the
degree counterterm `Λ·log`. -/
def selbergSource : ArithmeticFunction ℝ := vonMangoldt.pmul log + vonMangoldt * vonMangoldt

/-- `Λ₂ = μ ⋆ log²` (Selberg's identity). -/
theorem selbergSource_eq :
    selbergSource = (log.pmul log) * ((moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ) :=
  RHTower.vonMangoldt_pmul_log_add_mul_self

/-- **The renormalized source is nonnegative.** -/
theorem selbergSource_nonneg (n : ℕ) : 0 ≤ selbergSource n := by
  rw [selbergSource, ArithmeticFunction.add_apply, pmul_apply, mul_apply, log_apply]
  exact add_nonneg (mul_nonneg vonMangoldt_nonneg (Real.log_natCast_nonneg n))
    (Finset.sum_nonneg fun x _ => mul_nonneg vonMangoldt_nonneg vonMangoldt_nonneg)

/-- At a prime power the renormalized self-energy is an odd multiple of the squared degree:
`Λ₂(p^k) = (2k − 1)(log p)²`. -/
theorem selbergSource_prime_pow {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : 1 ≤ k) :
    selbergSource (p ^ k) = (2 * k - 1) * Real.log p ^ 2 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [selbergSource_eq, mul_apply, Nat.sum_divisorsAntidiagonal' (fun a b =>
    (log.pmul log) a * ((moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ) b),
    Nat.sum_divisors_prime_pow hp, Finset.sum_range_succ', Finset.sum_range_succ']
  have htail : ∑ i ∈ Finset.range j, (log.pmul log) (p ^ (j + 1) / p ^ (i + 1 + 1)) *
      ((moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ) (p ^ (i + 1 + 1)) = 0 :=
    Finset.sum_eq_zero fun i _ => by
      rw [intCoe_apply, moebius_apply_prime_pow hp (by omega), if_neg (by omega)]; simp
  rw [htail, zero_add, intCoe_apply, intCoe_apply, pow_zero, moebius_apply_one,
    zero_add, pow_one, moebius_apply_prime hp, Nat.div_one,
    Nat.pow_div (by omega) hp.pos, pmul_apply, pmul_apply, log_apply, log_apply]
  push_cast
  rw [show j + 1 - 1 = j by omega, Real.log_pow, Real.log_pow]
  push_cast
  ring

/-! ### The Dirichlet series of the renormalized source -/

theorem abscissaOfAbsConv_vonMangoldt_le :
    LSeries.abscissaOfAbsConv (fun n => (vonMangoldt n : ℂ)) ≤ 1 :=
  LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
    LSeriesSummable_vonMangoldt (by simpa using hy)

/-- **`L(Λ₂, s) = ζ″(s)/ζ(s)`** on `Re s > 1`. -/
theorem LSeries_selbergSource {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (selbergSource n : ℂ)) s = deriv (deriv riemannZeta) s / riemannZeta s := by
  set Λc : ℕ → ℂ := fun n => (vonMangoldt n : ℂ)
  have habs : LSeries.abscissaOfAbsConv Λc < s.re :=
    lt_of_le_of_lt abscissaOfAbsConv_vonMangoldt_le (by exact_mod_cast hs)
  have hs1 : s ≠ 1 := fun h => by rw [h, Complex.one_re] at hs; exact lt_irrefl _ hs
  -- `ζ` and `ζ′` are differentiable away from the pole
  have hdiff : DifferentiableOn ℂ riemannZeta {z | z ≠ 1} := fun z hz =>
    (differentiableAt_riemannZeta hz).differentiableWithinAt
  have hζ' : DifferentiableAt ℂ (deriv riemannZeta) s :=
    ((hdiff.deriv isOpen_ne).differentiableAt (isOpen_ne.mem_nhds hs1))
  have hζ0 : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  -- the counterterm: `L(Λ log) = −(L Λ)′ = (ζ′/ζ)′`
  have hLΛ : LSeries Λc =ᶠ[𝓝 s] fun z => -deriv riemannZeta z / riemannZeta z := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    exact LSeries_vonMangoldt_eq_deriv_riemannZeta_div hz
  have hlogMul : LSeries (LSeries.logMul Λc) s = deriv (logDeriv riemannZeta) s := by
    rw [← neg_neg (LSeries (LSeries.logMul Λc) s), ← LSeries_deriv habs, hLΛ.deriv_eq]
    have : (fun z => -deriv riemannZeta z / riemannZeta z) = fun z => -logDeriv riemannZeta z := by
      funext z; rw [logDeriv_apply, neg_div]
    rw [this]
    simp [deriv.neg']
  -- the coefficients split as counterterm plus square
  have hcoeff : (fun n => (selbergSource n : ℂ)) =
      LSeries.logMul Λc + fun n => (((vonMangoldt * vonMangoldt) n : ℝ) : ℂ) := by
    funext n
    simp only [selbergSource, ArithmeticFunction.add_apply, pmul_apply, log_apply, Pi.add_apply,
      LSeries.logMul, Λc]
    push_cast
    rw [Complex.ofReal_log (Nat.cast_nonneg n), Complex.ofReal_natCast]
    ring
  have hsq := ArithmeticCorrespondencePositivity.LSeries_vonMangoldtSelfConvolution_eq_logDeriv_sq hs
  have hsqSumm : LSeriesSummable (fun n => (((vonMangoldt * vonMangoldt) n : ℝ) : ℂ)) s := by
    have h := (LSeriesSummable_vonMangoldt hs).convolution (LSeriesSummable_vonMangoldt hs)
    have heq : (fun n => (((vonMangoldt * vonMangoldt) n : ℝ) : ℂ)) =
        LSeries.convolution (fun n => (vonMangoldt n : ℂ)) (fun n => (vonMangoldt n : ℂ)) := by
      have := RHTower.Sieve.complexCoeff_mul vonMangoldt vonMangoldt
      simp only [RHTower.Sieve.complexCoeff] at this
      exact this
    rw [heq]
    exact h
  rw [hcoeff, LSeries_add (LSeriesSummable_logMul_of_lt_re habs) hsqSumm, hlogMul, hsq,
    deriv_deriv_div_eq (differentiableAt_riemannZeta hs1) hζ' hζ0]
  ring

end

end GaloisForLFunctions.ArithmeticElectrostatics
