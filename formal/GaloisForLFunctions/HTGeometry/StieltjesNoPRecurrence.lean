import GaloisForLFunctions.HTGeometry.PRecursiveDFinite
import GaloisForLFunctions.HTGeometry.DifferentialAlgebraicOnClosure
import GaloisForLFunctions.RHTower.ZetaHypertranscendental
import GaloisForLFunctions.HTGeometry.EulerQGammaHypertranscendence

/-!
# The Stieltjes constants satisfy no linear recurrence with polynomial coefficients

`f1-inversion-single-prime-stieltjes-collapse`, §4.

The function `z ↦ z·ζ(1 + z)` extends to an entire function whose Taylor coefficients are the
Stieltjes constants up to the factor `(−1)^n/n!`.  It is hypertranscendental, because a
differential relation for it would give one for `ζ(1 + z)` off the pole, hence one for `ζ` on
`ℂ \ {1}`, hence — after multiplying the witnessing polynomial by `X₀ − 1` — a global one,
contradicting Hilbert's theorem.  The P-recursive-to-D-finite dictionary then forbids any linear
recurrence with polynomial coefficients among the Stieltjes constants.
-/

open Complex Filter Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ## The entire completion of the zeta pole -/

/-- `z ↦ z·ζ(1 + z)`, completed at the origin by its limit `1`. -/
def zetaPoleCompletion : ℂ → ℂ :=
  Function.update (fun z : ℂ => z * riemannZeta (1 + z)) 0 1

theorem zetaPoleCompletion_apply {z : ℂ} (hz : z ≠ 0) :
    zetaPoleCompletion z = z * riemannZeta (1 + z) :=
  Function.update_of_ne hz _ _

theorem tendsto_zetaPole : Tendsto (fun z : ℂ => z * riemannZeta (1 + z)) (𝓝[≠] 0) (𝓝 1) := by
  have hmap : Tendsto (fun z : ℂ => 1 + z) (𝓝[≠] (0 : ℂ)) (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hfull : Tendsto (fun z : ℂ => 1 + z) (𝓝 (0 : ℂ)) (𝓝 (1 + 0)) :=
        tendsto_const_nhds.add tendsto_id
      rw [add_zero] at hfull
      exact hfull.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      intro hc
      apply hz
      have h1 : (1 : ℂ) + z = 1 := hc
      refine Set.mem_singleton_iff.mpr ?_
      linear_combination h1
  have hcomp := riemannZeta_residue_one.comp hmap
  refine hcomp.congr fun z => ?_
  simp only [Function.comp_apply]
  ring_nf

theorem differentiable_zetaPoleCompletion : Differentiable ℂ zetaPoleCompletion := by
  have hkey : DifferentiableOn ℂ zetaPoleCompletion Set.univ := by
    refine (Complex.differentiableOn_compl_singleton_and_continuousAt_iff
      (c := (0 : ℂ)) (s := Set.univ) Filter.univ_mem).mp ⟨?_, ?_⟩
    · intro z hz
      have hzne : z ≠ 0 := by
        intro hc
        exact hz.2 (by simp [hc])
      have hz1 : (1 : ℂ) + z ≠ 1 := by
        intro hc
        exact hzne (by linear_combination hc)
      have hd : DifferentiableAt ℂ (fun w : ℂ => w * riemannZeta (1 + w)) z := by
        refine differentiableAt_id.mul ?_
        exact (differentiableAt_riemannZeta hz1).comp z
          ((differentiableAt_const (1 : ℂ)).add differentiableAt_id)
      refine (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
      filter_upwards [isOpen_ne.mem_nhds hzne] with w hw
      exact zetaPoleCompletion_apply hw
    · rw [zetaPoleCompletion]
      exact continuousAt_update_same.mpr tendsto_zetaPole
  intro z
  exact (hkey.differentiableAt Filter.univ_mem)


/-! ## From a punctured relation to a global one -/

theorem differentiallyAlgebraicOn_id (U : Set ℂ) :
    DifferentiallyAlgebraicOn (fun z : ℂ => z) U := by
  refine ⟨0, MvPolynomial.X (1 : Fin 2) - MvPolynomial.X (0 : Fin 2), ?_, ?_⟩
  · intro hc
    have hcoeff := congrArg (MvPolynomial.coeff (Finsupp.single (1 : Fin 2) 1)) hc
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_X, MvPolynomial.coeff_X,
      MvPolynomial.coeff_zero] at hcoeff
    rw [if_pos rfl, if_neg] at hcoeff
    · norm_num at hcoeff
    · intro hcc
      have := congrArg (fun g : Fin 2 →₀ ℕ => g 1) hcc
      simp at this
  · intro z _
    rw [map_sub, MvPolynomial.eval_X, MvPolynomial.eval_X]
    have h0 : (Fin.cons (α := fun _ : Fin 2 => ℂ) z
        fun j : Fin 1 => iteratedDeriv (j : ℕ) (fun w : ℂ => w) z) (0 : Fin 2) = z := rfl
    have h1 : (Fin.cons (α := fun _ : Fin 2 => ℂ) z
        fun j : Fin 1 => iteratedDeriv (j : ℕ) (fun w : ℂ => w) z) (1 : Fin 2) = z := by
      show iteratedDeriv 0 (fun w : ℂ => w) z = z
      simp
    rw [h0, h1, sub_self]

/-! ## Hypertranscendence of the completion -/

theorem hypertranscendental_zetaPoleCompletion :
    GaloisForLFunctions.Hypertranscendental zetaPoleCompletion := by
  intro hDA
  have hUo : IsOpen {z : ℂ | z ≠ 0} := isOpen_ne
  have hUconn : IsConnected {z : ℂ | z ≠ 0} := by
    have h : ({z : ℂ | z ≠ 0}) = ({(0 : ℂ)}ᶜ) := rfl
    rw [h]
    exact isConnected_compl_singleton_of_one_lt_rank
      (by simp [Complex.rank_real_complex]) 0
  have hUne : ({z : ℂ | z ≠ 0}).Nonempty := ⟨1, one_ne_zero⟩
  have hUinf : ({z : ℂ | z ≠ 0}).Infinite := by
    have h : ({z : ℂ | z ≠ 0}) = ({(0 : ℂ)}ᶜ) := rfl
    rw [h]
    exact Set.Finite.infinite_compl (Set.finite_singleton _)
  have hGon : DifferentiallyAlgebraicOn zetaPoleCompletion {z : ℂ | z ≠ 0} := by
    obtain ⟨n, P, hP0, hPz⟩ := hDA
    exact ⟨n, P, hP0, fun z _ => hPz z⟩
  have hGan : AnalyticOnNhd ℂ zetaPoleCompletion {z : ℂ | z ≠ 0} :=
    fun z _ => (Complex.analyticOnNhd_univ_iff_differentiable.mpr
      differentiable_zetaPoleCompletion) z (Set.mem_univ z)
  have hidan : AnalyticOnNhd ℂ (fun z : ℂ => z) {z : ℂ | z ≠ 0} :=
    fun z _ => analyticAt_id
  have hdiv := differentiallyAlgebraicOn_div hUo hUconn.isPreconnected hUne hUinf
    hGan hidan (fun z hz => hz) hGon (differentiallyAlgebraicOn_id _)
  have hzeta1 : DifferentiallyAlgebraicOn (fun z : ℂ => riemannZeta (1 + z))
      {z : ℂ | z ≠ 0} := by
    refine DifferentiallyAlgebraicOn.congr hUo (fun z hz => ?_) hdiv
    have hz0 : z ≠ 0 := hz
    rw [zetaPoleCompletion_apply hz0]
    field_simp
  have hshift := DifferentiallyAlgebraicOn.comp_add_const hzeta1 (-1)
  have hset : {z : ℂ | z + (-1) ∈ {z : ℂ | z ≠ 0}} = {z : ℂ | z ≠ 1} := by
    ext z
    simp only [Set.mem_setOf_eq, ne_eq]
    constructor
    · intro h hc
      exact h (by rw [hc]; ring)
    · intro h hc
      exact h (by linear_combination hc)
  rw [hset] at hshift
  have hzeta : DifferentiallyAlgebraicOn riemannZeta {z : ℂ | z ≠ 1} := by
    refine DifferentiallyAlgebraicOn.congr isOpen_ne (fun z _ => ?_) hshift
    congr 1
    ring
  have hzan : AnalyticOnNhd ℂ riemannZeta (({1} : Set ℂ)ᶜ) := by
    intro z hz
    exact analyticOn_riemannZeta z (by simpa using hz)
  have hVsub : {z : ℂ | z ≠ 1} ⊆ (({1} : Set ℂ)ᶜ) := fun z hz => by simpa using hz
  exact hypertranscendental_riemannZeta
    (differentiallyAlgebraic_of_on_compl_singleton hzan isOpen_ne ⟨0, by norm_num⟩ hVsub hzeta)


/-! ## The Stieltjes constants -/

/-- The Stieltjes constants, read off the Taylor expansion of `z·ζ(1 + z)` at the origin:
`z·ζ(1+z) = 1 + ∑ₙ (−1)ⁿ γₙ z^{n+1}/n!`. -/
def stieltjesGamma (n : ℕ) : ℂ :=
  (-1) ^ n * (n.factorial : ℂ) * PowerSeries.coeff (n + 1) (taylorSeries zetaPoleCompletion)

theorem coeff_taylorSeries_succ_eq (n : ℕ) :
    PowerSeries.coeff (n + 1) (taylorSeries zetaPoleCompletion)
      = (-1) ^ n * stieltjesGamma n / (n.factorial : ℂ) := by
  have hfac : ((n.factorial : ℂ)) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have hsign2 : ((-1 : ℂ)) ^ (n * 2) = 1 := by
    rw [mul_comm, pow_mul]
    norm_num
  rw [stieltjesGamma]
  field_simp
  linear_combination
    (-(PowerSeries.coeff (n + 1) (taylorSeries zetaPoleCompletion))) * hsign2

theorem eval_risingPoly_mul_factorial (n : ℕ) : ∀ j : ℕ,
    (risingPoly j).eval (n : ℂ) * (n.factorial : ℂ) = ((n + j).factorial : ℂ)
  | 0 => by simp [risingPoly]
  | (j + 1) => by
      rw [eval_risingPoly_succ]
      have hstep : ((n + (j + 1)).factorial : ℂ)
          = ((n + j : ℕ) : ℂ) * ((n + j).factorial : ℂ) + ((n + j).factorial : ℂ) := by
        have hidx : n + (j + 1) = (n + j) + 1 := by omega
        rw [hidx, Nat.factorial_succ]
        push_cast
        ring
      rw [hstep, ← eval_risingPoly_mul_factorial n j]
      push_cast
      ring

theorem comp_X_sub_one_ne_zero {p : Polynomial ℂ} (hp : p ≠ 0) :
    p.comp (Polynomial.X - 1) ≠ 0 := by
  intro hc
  refine hp (Polynomial.funext fun a => ?_)
  have h := congrArg (Polynomial.eval (a + 1)) hc
  rw [Polynomial.eval_comp, Polynomial.eval_zero, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_one, add_sub_cancel_right] at h
  simpa using h

/-- **P-recursiveness transfers from the Stieltjes constants to the Taylor coefficients.** -/
theorem pRecursive_coeff_of_pRecursive_stieltjes
    (h : PRecursive stieltjesGamma) :
    PRecursive (fun n => PowerSeries.coeff n (taylorSeries zetaPoleCompletion)) := by
  obtain ⟨d, N, p, ⟨j₀, hj₀d, hj₀⟩, hrec⟩ := h
  refine ⟨d, N + 1, fun j => Polynomial.C ((-1 : ℂ) ^ j) * (p j).comp (Polynomial.X - 1)
      * (risingPoly j).comp (Polynomial.X - 1), ⟨j₀, hj₀d, ?_⟩, ?_⟩
  · refine mul_ne_zero (mul_ne_zero ?_ (comp_X_sub_one_ne_zero hj₀))
      (comp_X_sub_one_ne_zero (risingPoly_ne_zero j₀))
    simp only [ne_eq, Polynomial.C_eq_zero]
    exact pow_ne_zero j₀ (by norm_num)
  · intro k hk
    have hk1 : 1 ≤ k := by omega
    set n : ℕ := k - 1 with hn
    have hkn : k = n + 1 := by omega
    have hnN : N ≤ n := by omega
    have hcast : ((k : ℂ)) - 1 = (n : ℂ) := by
      rw [hkn]
      push_cast
      ring
    have hfac : ((n.factorial : ℂ)) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero n
    have hterm : ∀ j ∈ Finset.range (d + 1),
        (Polynomial.C ((-1 : ℂ) ^ j) * (p j).comp (Polynomial.X - 1)
            * (risingPoly j).comp (Polynomial.X - 1)).eval (k : ℂ)
          * PowerSeries.coeff (k + j) (taylorSeries zetaPoleCompletion)
        = ((-1 : ℂ)) ^ n / (n.factorial : ℂ) * ((p j).eval (n : ℂ) * stieltjesGamma (n + j)) := by
      intro j _
      rw [Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp,
        Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one, hcast]
      have hidx : k + j = (n + j) + 1 := by omega
      rw [hidx, coeff_taylorSeries_succ_eq]
      have hrise := eval_risingPoly_mul_factorial n j
      have hsign : ((-1 : ℂ)) ^ (n + j) = ((-1 : ℂ)) ^ n * ((-1 : ℂ)) ^ j := by
        rw [pow_add]
      have hfacnj : (((n + j).factorial : ℂ)) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero (n + j)
      rw [hsign]
      field_simp
      have hsignj : ((-1 : ℂ)) ^ (j * 2) = 1 := by
        rw [mul_comm, pow_mul]
        norm_num
      linear_combination ((p j).eval (n : ℂ) * stieltjesGamma (n + j)) * hrise
        + ((p j).eval (n : ℂ) * (risingPoly j).eval (n : ℂ) * stieltjesGamma (n + j)
            * (n.factorial : ℂ)) * hsignj
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    have hzero : ∑ j ∈ Finset.range (d + 1), (p j).eval (n : ℂ) * stieltjesGamma (n + j) = 0 :=
      hrec n hnN
    rw [hzero, mul_zero]

/-- **§4.**  The Stieltjes constants satisfy no linear recurrence with polynomial coefficients. -/
theorem not_pRecursive_stieltjesGamma : ¬ PRecursive stieltjesGamma := by
  intro h
  exact not_pRecursive_taylorSeries_of_hypertranscendental differentiable_zetaPoleCompletion
    hypertranscendental_zetaPoleCompletion (pRecursive_coeff_of_pRecursive_stieltjes h)

end GaloisForLFunctions.HTGeometry
