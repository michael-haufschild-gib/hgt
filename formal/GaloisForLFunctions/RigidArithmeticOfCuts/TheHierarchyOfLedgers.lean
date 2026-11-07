import GaloisForLFunctions.RHTower.CompactOpenKolchinWardChargeEscape
import GaloisForLFunctions.RHTower.PrimeShiftResidueClosability
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# The hierarchy of ledgers

Reading the `k`-fold convolution `Λ^{∗k}` through a floor has generating function
`ζ(s) A(s)^k`, with `A = −ζ′/ζ`. At a zero of multiplicity `m` this function has order `m − k`.

* `k = 1` is **blind**: `ζ A = −ζ′` is holomorphic at every zero. This is the blindness of every linear
  floor functional, and it holds for every multiplicity.
* `k ≥ 2` **sees** a zero of multiplicity `m < k`, through a pole of order `k − m`. At a simple zero the
  leading coefficient is `(−1)^k ζ′(ρ)`.

So `k = 1` is the only level blind to all zeros. The sum in Selberg's identity `ζ(A² − A′) = ζ″` is again
holomorphic: the pieces see the zero and their sum does not. Any exact ledger, a differential polynomial in
`ζ`, is holomorphic off `s = 1`, so an exact ledger never sees a zero. Seeing a zero costs the exact value.
-/

open Complex Filter Topology
open ArithmeticFunction (vonMangoldt)

noncomputable section

namespace GaloisForLFunctions.RigidArithmeticOfCuts

/-- The Dirichlet series `A = −ζ′/ζ` of `Λ`. -/
def vonMangoldtSymbol (s : ℂ) : ℂ := -logDeriv riemannZeta s

/-- The symbol `ζ A^k` of the `k`-ledger. -/
def ledgerSymbol (k : ℕ) (s : ℂ) : ℂ := riemannZeta s * vonMangoldtSymbol s ^ k

theorem analyticAt_riemannZeta {ρ : ℂ} (hρ : ρ ≠ 1) : AnalyticAt ℂ riemannZeta ρ := by
  have hopen : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
  have hd : DifferentiableOn ℂ riemannZeta ({1}ᶜ : Set ℂ) := fun z hz =>
    (differentiableAt_riemannZeta hz).differentiableWithinAt
  exact hd.analyticAt (hopen.mem_nhds hρ)

theorem meromorphicAt_logDeriv_riemannZeta {ρ : ℂ} (hρ : ρ ≠ 1) :
    MeromorphicAt (logDeriv riemannZeta) ρ := by
  have h := analyticAt_riemannZeta hρ
  have hderiv : AnalyticAt ℂ (deriv riemannZeta) ρ := h.deriv
  have : logDeriv riemannZeta = fun z => deriv riemannZeta z / riemannZeta z := rfl
  rw [this]
  exact hderiv.meromorphicAt.div h.meromorphicAt

theorem meromorphicAt_vonMangoldtSymbol {ρ : ℂ} (hρ : ρ ≠ 1) :
    MeromorphicAt vonMangoldtSymbol ρ :=
  (meromorphicAt_logDeriv_riemannZeta hρ).neg

/-- The order of `A` at a zero of `ζ` is `−1`, for every multiplicity. -/
theorem meromorphicOrderAt_vonMangoldtSymbol {ρ : ℂ} (hρ : ρ ≠ 1) (hz : riemannZeta ρ = 0) :
    meromorphicOrderAt vonMangoldtSymbol ρ = ((-1 : ℤ) : WithTop ℤ) := by
  have h := RHTower.meromorphicOrderAt_logDeriv_eq_neg_one_of_analyticAt
    (analyticAt_riemannZeta hρ) (RHTower.analyticOrderAt_riemannZeta_ne_top hρ) hz
  have hfun : vonMangoldtSymbol = (fun _ => (-1 : ℂ)) * logDeriv riemannZeta := by
    funext s
    simp [vonMangoldtSymbol]
  rw [hfun, meromorphicOrderAt_mul analyticAt_const.meromorphicAt
    (meromorphicAt_logDeriv_riemannZeta hρ), h]
  have h1 : meromorphicOrderAt (fun _ : ℂ => (-1 : ℂ)) ρ = ((0 : ℤ) : WithTop ℤ) :=
    (meromorphicOrderAt_eq_int_iff analyticAt_const.meromorphicAt).mpr
      ⟨fun _ => -1, analyticAt_const, by norm_num, by simp⟩
  rw [h1]
  norm_cast

/-- **The order law.** At a zero of multiplicity `m`, the symbol `ζ A^k` has order `m − k`. -/
theorem meromorphicOrderAt_ledgerSymbol (k : ℕ) {ρ : ℂ} (hρ : ρ ≠ 1) (hz : riemannZeta ρ = 0)
    {m : ℕ} (hm : analyticOrderAt riemannZeta ρ = m) :
    meromorphicOrderAt (ledgerSymbol k) ρ = (((m : ℤ) - (k : ℤ) : ℤ) : WithTop ℤ) := by
  have hζ := analyticAt_riemannZeta hρ
  have hA := meromorphicAt_vonMangoldtSymbol hρ
  have hfun : ledgerSymbol k = riemannZeta * vonMangoldtSymbol ^ k := rfl
  rw [hfun, meromorphicOrderAt_mul hζ.meromorphicAt (hA.pow k), meromorphicOrderAt_pow hA,
    meromorphicOrderAt_vonMangoldtSymbol hρ hz, hζ.meromorphicOrderAt_eq, hm, ENat.map_coe]
  have hval : (m : ℤ) + (k : ℤ) * (-1) = (m : ℤ) - (k : ℤ) := by ring
  exact_mod_cast hval

/-- **`k = 1` is blind at every zero.** -/
theorem blind_of_linear {ρ : ℂ} (hρ : ρ ≠ 1) (hz : riemannZeta ρ = 0) {m : ℕ} (hm1 : 1 ≤ m)
    (hm : analyticOrderAt riemannZeta ρ = m) : 0 ≤ meromorphicOrderAt (ledgerSymbol 1) ρ := by
  rw [meromorphicOrderAt_ledgerSymbol 1 hρ hz hm]
  have : (0 : ℤ) ≤ (m : ℤ) - ((1 : ℕ) : ℤ) := by push_cast; omega
  exact_mod_cast this

/-- **A level above the multiplicity sees the zero.** -/
theorem sees_of_lt {k m : ℕ} (hkm : m < k) {ρ : ℂ} (hρ : ρ ≠ 1) (hz : riemannZeta ρ = 0)
    (hm : analyticOrderAt riemannZeta ρ = m) : meromorphicOrderAt (ledgerSymbol k) ρ < 0 := by
  rw [meromorphicOrderAt_ledgerSymbol k hρ hz hm]
  have : (m : ℤ) - (k : ℤ) < 0 := by omega
  exact_mod_cast this

/-- **The linear symbol is `−ζ′`, holomorphic off the pole.** -/
theorem ledgerSymbol_one_eq {s : ℂ} (hs : riemannZeta s ≠ 0) :
    ledgerSymbol 1 s = -deriv riemannZeta s := by
  simp only [ledgerSymbol, vonMangoldtSymbol, pow_one, logDeriv_apply]
  field_simp

/-- The difference quotient of `ζ` at a zero. -/
private lemma tendsto_zeta_div {ρ : ℂ} (hρ : ρ ≠ 1) (hz : riemannZeta ρ = 0) :
    Tendsto (fun s => riemannZeta s / (s - ρ)) (𝓝[≠] ρ) (𝓝 (deriv riemannZeta ρ)) := by
  have h := (differentiableAt_riemannZeta hρ).hasDerivAt.tendsto_slope
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s _
  simp only [slope_def_field, hz, sub_zero]

/-- **The leading coefficient at a simple zero.** `(s − ρ)^{k−1} ζ A^k → (−1)^k ζ′(ρ)`. -/
theorem tendsto_mul_ledgerSymbol {ρ : ℂ} (hρ : ρ ≠ 1) (hz : riemannZeta ρ = 0)
    (hd : deriv riemannZeta ρ ≠ 0) (k : ℕ) :
    Tendsto (fun s => (s - ρ) ^ k * ledgerSymbol (k + 1) s) (𝓝[≠] ρ)
      (𝓝 ((-1) ^ (k + 1) * deriv riemannZeta ρ)) := by
  have h1 := tendsto_zeta_div hρ hz
  have hderiv : Tendsto (deriv riemannZeta) (𝓝[≠] ρ) (𝓝 (deriv riemannZeta ρ)) :=
    (analyticAt_riemannZeta hρ).deriv.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun s => (s - ρ) * logDeriv riemannZeta s) (𝓝[≠] ρ) (𝓝 1) := by
    have h3 := hderiv.div h1 hd
    rw [div_self hd] at h3
    refine h3.congr' ?_
    have hne : ∀ᶠ s in 𝓝[≠] ρ, riemannZeta s ≠ 0 :=
      ((analyticAt_riemannZeta hρ).eventually_eq_zero_or_eventually_ne_zero).resolve_left
        (fun hev => (RHTower.analyticOrderAt_riemannZeta_ne_top hρ)
          (analyticOrderAt_eq_top.mpr hev))
    filter_upwards [hne, self_mem_nhdsWithin] with s hs hs0
    have hsρ : s - ρ ≠ 0 := sub_ne_zero.mpr hs0
    simp only [Pi.div_apply, logDeriv_apply]
    field_simp
  have h4 := (h2.neg.pow (k + 1)).mul h1
  have hval : (-1 : ℂ) ^ (k + 1) * deriv riemannZeta ρ = (-1) ^ (k + 1) * deriv riemannZeta ρ := rfl
  refine h4.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs0
  have hsρ : s - ρ ≠ 0 := sub_ne_zero.mpr hs0
  simp only [ledgerSymbol, vonMangoldtSymbol]
  rw [neg_pow ((s - ρ) * logDeriv riemannZeta s), neg_pow (logDeriv riemannZeta s), mul_pow]
  field_simp
  ring

/-- **Selberg's identity is blind.** `ζ (A² − A′) = ζ″`, holomorphic at every zero: the double pole of
`A²` and that of `A′` cancel at a simple zero, and the pieces see what the sum does not. -/
theorem riemannZeta_mul_selberg {s : ℂ} (hs1 : s ≠ 1) (hs : riemannZeta s ≠ 0) :
    riemannZeta s * (vonMangoldtSymbol s ^ 2 - deriv vonMangoldtSymbol s) =
      deriv (deriv riemannZeta) s := by
  have hζ := analyticAt_riemannZeta hs1
  have hd : DifferentiableAt ℂ riemannZeta s := hζ.differentiableAt
  have hdd : DifferentiableAt ℂ (deriv riemannZeta) s := hζ.deriv.differentiableAt
  have hA : deriv vonMangoldtSymbol s =
      -((deriv (deriv riemannZeta) s * riemannZeta s - deriv riemannZeta s * deriv riemannZeta s) /
        riemannZeta s ^ 2) := by
    have hfun : vonMangoldtSymbol = fun z => -(deriv riemannZeta z / riemannZeta z) := by
      funext z
      simp [vonMangoldtSymbol, logDeriv_apply]
    have h : HasDerivAt (fun z => -(deriv riemannZeta z / riemannZeta z))
        (-((deriv (deriv riemannZeta) s * riemannZeta s - deriv riemannZeta s * deriv riemannZeta s) /
          riemannZeta s ^ 2)) s := (hdd.hasDerivAt.div hd.hasDerivAt hs).neg
    rw [hfun, h.deriv]
  rw [hA]
  simp only [vonMangoldtSymbol, logDeriv_apply]
  field_simp
  ring

/-- `L(Λ, s) = A(s)` on `Re s > 1`. -/
theorem lseries_vonMangoldt_eq {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (vonMangoldt n : ℂ)) s = vonMangoldtSymbol s := by
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]
  simp [vonMangoldtSymbol, logDeriv_apply, neg_div]

end GaloisForLFunctions.RigidArithmeticOfCuts
