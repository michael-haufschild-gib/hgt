import GaloisForLFunctions.MultiplicativePositivityGeometry.SimplePoleClassification
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.HarmonicCouplingForcesSourceBlindness

/-!
# The boundary divisor of ζ is the Dirac mass at the origin

On `Re s = 1 + x` with `x > 0`, `Re(−ζ'/ζ)(1 + x + iu)` is the cosine trace of the von Mangoldt
weights `Λ(n) n^{-1-x}` on the frequencies `log n` (`zetaRealLogDeriv_eq_cosineTrace`). Its
normalized boundary limit is `D_ζ(u)`, the pole order minus the zero order of `ζ` at `1 + iu`
(`tendsto_zetaRealLogDeriv_boundary`). So `D_ζ` is a boundary divisor (`zeta_isBoundaryDivisor`)
and even positive definite. It is integer valued, `D_ζ 0 = 1`, and `D_ζ ≤ 0` off the origin.
The simple-pole classification then gives `D_ζ = 1_{0}` (`zetaBoundaryDivisor_eq`), i.e.
`ζ(1 + iu) ≠ 0` for `u ≠ 0` (`riemannZeta_boundary_ne_zero_of_posDef`).

The inputs are `Λ ≥ 0`, the residue at `1` and local analytic factorization; positivity enters only
as positive definiteness of the boundary divisor. Equivalently, the normalized prime measure
`x Σ Λ(n) n^{-1-x} δ_{log n}` has asymptotically orthonormal characters at distinct heights
(`zeta_boundary_gram_tendsto`).
-/

open Filter Topology Complex
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri

namespace GaloisForLFunctions.MultiplicativePositivityGeometry

/-- Damped von Mangoldt weights `Λ(n) n^{-(1+x)}`. -/
noncomputable def zetaBoundaryWeight (x : ℝ) (n : ℕ) : ℝ :=
  (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + x))

/-- The logarithmic frequencies `log n`. -/
noncomputable def logFrequency (n : ℕ) : ℝ := Real.log n

/-- The boundary divisor of `ζ` on `Re s = 1`: pole order minus zero order at `1 + iu`. -/
noncomputable def zetaBoundaryDivisor (u : ℝ) : ℝ :=
  (zetaBoundaryPoleOrder u : ℝ) - (zetaBoundaryZeroOrder u : ℝ)

theorem zetaBoundaryWeight_nonneg (x : ℝ) (n : ℕ) : 0 ≤ zetaBoundaryWeight x n :=
  mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)

private theorem re_term_eq_weight {x : ℝ} (u : ℝ) (n : ℕ) :
    (LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
      (((1 + x : ℝ) : ℂ) + (u : ℂ) * I) n).re =
      zetaBoundaryWeight x n * Real.cos (logFrequency n * u) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [zetaBoundaryWeight]
  · rw [RHTower.re_lseries_term_vonMangoldt hn (1 + x) u, zetaBoundaryWeight, logFrequency,
      mul_comm (Real.log n) u]
    ring

theorem summable_zetaBoundaryWeight {x : ℝ} (hx : 0 < x) : Summable (zetaBoundaryWeight x) := by
  have hre : 1 < (((1 + x : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I).re := by simp; linarith
  have hs := Complex.reCLM.summable (ArithmeticFunction.LSeriesSummable_vonMangoldt hre)
  refine hs.congr fun n => ?_
  have := re_term_eq_weight (x := x) 0 n
  simp only [mul_zero, Real.cos_zero, mul_one] at this
  exact this

/-- `Re(−ζ'/ζ)` on `Re s = 1 + x` is the cosine trace of the damped von Mangoldt weights. -/
theorem zetaRealLogDeriv_eq_cosineTrace {x : ℝ} (hx : 0 < x) (u : ℝ) :
    zetaRealLogDeriv (1 + x) u = cosineTrace (zetaBoundaryWeight x) logFrequency u := by
  have hre : 1 < (((1 + x : ℝ) : ℂ) + (u : ℂ) * I).re := by simp; linarith
  have hL := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hre
  have hs := ArithmeticFunction.LSeriesSummable_vonMangoldt hre
  unfold zetaRealLogDeriv cosineTrace
  have hneg : -deriv riemannZeta (((1 + x : ℝ) : ℂ) + (u : ℂ) * I) /
      riemannZeta (((1 + x : ℝ) : ℂ) + (u : ℂ) * I) =
      LSeries (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
        (((1 + x : ℝ) : ℂ) + (u : ℂ) * I) := by
    rw [hL, neg_div]
  rw [hneg, LSeries, Complex.re_tsum hs]
  exact tsum_congr fun n => re_term_eq_weight u n

/-- The damping `x ↦ 1 + x` carries `𝓝[>] 0` to `𝓝[>] 1`. -/
theorem tendsto_one_add_nhdsGT : Tendsto (fun x : ℝ => 1 + x) (𝓝[>] 0) (𝓝[>] 1) := by
  have h := ((continuous_const_add (1 : ℝ)).continuousWithinAt
    (s := Set.Ioi 0) (x := 0)).tendsto_nhdsWithin (t := Set.Ioi 1)
    (fun x hx => by simpa using (show (1 : ℝ) < 1 + x by linarith [Set.mem_Ioi.mp hx]))
  simpa using h

/-- `D_ζ` is the boundary divisor of the damped von Mangoldt weights. -/
theorem zeta_isBoundaryDivisor :
    IsBoundaryDivisor logFrequency zetaBoundaryWeight zetaBoundaryDivisor where
  nonneg x _ n := zetaBoundaryWeight_nonneg x n
  summable _ hx := summable_zetaBoundaryWeight hx
  tendsto u := by
    have h := (tendsto_zetaRealLogDeriv_boundary u).comp tendsto_one_add_nhdsGT
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [Function.comp_apply, add_sub_cancel_left]
    rw [zetaRealLogDeriv_eq_cosineTrace (Set.mem_Ioi.mp hx)]

theorem zetaBoundaryDivisor_isEvenPosDef : IsEvenPosDef zetaBoundaryDivisor :=
  zeta_isBoundaryDivisor.isEvenPosDef

theorem zetaBoundaryDivisor_zero : zetaBoundaryDivisor 0 = 1 := by
  simp [zetaBoundaryDivisor, zetaBoundaryPoleOrder, zetaBoundaryZeroOrder]

theorem zetaBoundaryDivisor_intValued (u : ℝ) : ∃ n : ℤ, zetaBoundaryDivisor u = n :=
  ⟨(zetaBoundaryPoleOrder u : ℤ) - zetaBoundaryZeroOrder u, by
    simp [zetaBoundaryDivisor]⟩

theorem zetaBoundaryDivisor_nonpos {u : ℝ} (hu : u ≠ 0) : zetaBoundaryDivisor u ≤ 0 := by
  simp [zetaBoundaryDivisor, zetaBoundaryPoleOrder, hu]

/-- **The boundary divisor of ζ is the Dirac mass at the origin.** -/
theorem zetaBoundaryDivisor_eq (u : ℝ) :
    zetaBoundaryDivisor u = if u = 0 then 1 else 0 :=
  boundary_eq_delta_of_no_pole zetaBoundaryDivisor_isEvenPosDef zetaBoundaryDivisor_zero
    zetaBoundaryDivisor_intValued (fun _ hv => zetaBoundaryDivisor_nonpos hv) u

theorem zetaBoundaryZeroOrder_eq_zero_of_posDef (u : ℝ) : zetaBoundaryZeroOrder u = 0 := by
  by_cases hu : u = 0
  · simp [zetaBoundaryZeroOrder, hu]
  · have h := zetaBoundaryDivisor_eq u
    simp only [hu, if_false, zetaBoundaryDivisor, zetaBoundaryPoleOrder, Nat.cast_zero,
      zero_sub, neg_eq_zero, Nat.cast_eq_zero] at h
    exact h

private theorem analyticOrderAt_riemannZeta_ne_top {w : ℂ} (hw : w ≠ 1) :
    analyticOrderAt riemannZeta w ≠ ⊤ := by
  intro htop
  have hlocal : riemannZeta =ᶠ[𝓝 w] (0 : ℂ → ℂ) := by
    filter_upwards [analyticOrderAt_eq_top.mp htop] with z hz
    simpa using hz
  have hpre : IsPreconnected ({(1 : ℂ)}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
  have hana : AnalyticOnNhd ℂ riemannZeta ({(1 : ℂ)}ᶜ : Set ℂ) :=
    fun z hz => HTGeometry.analyticAt_riemannZeta hz
  have hglobal : Set.EqOn riemannZeta 0 ({(1 : ℂ)}ᶜ : Set ℂ) :=
    hana.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hpre (by simpa using hw) hlocal
  have h2 : riemannZeta (2 : ℂ) = 0 := by
    simpa using hglobal (show (2 : ℂ) ∈ ({(1 : ℂ)}ᶜ : Set ℂ) by norm_num)
  exact riemannZeta_ne_zero_of_one_lt_re (by norm_num) h2

/-- **`ζ(1 + iu) ≠ 0` from positive definiteness of the boundary divisor.** -/
theorem riemannZeta_boundary_ne_zero_of_posDef {u : ℝ} (hu : u ≠ 0) :
    riemannZeta (1 + (u : ℂ) * I) ≠ 0 := by
  have hz := zetaBoundaryZeroOrder_eq_zero_of_posDef u
  simp only [zetaBoundaryZeroOrder, hu, if_false] at hz
  have hρ1 : (1 + (u : ℂ) * I) ≠ 1 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    exact hu this
  have hord : analyticOrderAt riemannZeta (1 + (u : ℂ) * I) = 0 := by
    rcases ENat.toNat_eq_zero.mp hz with h | h
    · exact h
    · exact absurd h (analyticOrderAt_riemannZeta_ne_top hρ1)
  exact (HTGeometry.analyticAt_riemannZeta hρ1).analyticOrderAt_eq_zero.mp hord

/-- **Prime phases at distinct heights are asymptotically orthonormal on `Re s = 1`.** For
distinct heights `u₀, …, u_{N-1}`, the normalized Gram matrix
`x · Σ Λ(n) n^{-1-x} cos((uᵢ − uⱼ) log n)` tends to the identity as `x ↓ 0`. -/
theorem zeta_boundary_gram_tendsto {N : ℕ} {u : Fin N → ℝ} (hu : Function.Injective u)
    (i j : Fin N) :
    Tendsto (fun x => x * cosineTrace (zetaBoundaryWeight x) logFrequency (u i - u j))
      (𝓝[>] 0) (𝓝 (if i = j then 1 else 0)) := by
  have h := zeta_isBoundaryDivisor.tendsto (u i - u j)
  have hiff : u i - u j = 0 ↔ i = j := by rw [sub_eq_zero, hu.eq_iff]
  rw [zetaBoundaryDivisor_eq] at h
  simpa only [hiff] using h

end GaloisForLFunctions.MultiplicativePositivityGeometry
