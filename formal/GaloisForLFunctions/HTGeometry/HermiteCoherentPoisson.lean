import GaloisForLFunctions.HTGeometry.HermiteL2Expansion
import GaloisForLFunctions.HTGeometry.HermiteCoordinateMoments

/-!
# Translated Gaussians have Poisson-distributed Hermite energy

The translated Gaussian `ψ_y(x) = e^{-π(x-y)²}` (`coherentGauss`) is an eigenvector of the
annihilation operator `B = 2πx + ∂` with eigenvalue `2πy` (`annihilationCLM_coherentGauss`).  Since
the creation operator is the transpose of `B` for the bilinear pairing and raises the Hermite index,
the pairings with the unnormalized Hermite functions are a geometric sequence,
`⟨ψ_y, h_n⟩ = yⁿ ⟨ψ_y, h_0⟩` (`schwartzPair_coherentGauss_hermiteSchwartz`), while
`‖h_n‖² = n!/πⁿ ‖h_0‖²` (`norm_sq_toLp_hermiteSchwartz`).  Hence

`|c_n(ψ_y)|² = |c_0(ψ_y)|² (πy²)ⁿ/n!`   (`norm_sq_hermiteCoeff_coherentGauss`),

and Parseval gives `|c_0(ψ_y)|² = ‖ψ_y‖² e^{-πy²}`: the Hermite energy of `ψ_y` is the Poisson law of
parameter `πy²` (`hasSum_norm_sq_hermiteCoeff_coherentGauss`).
-/

open scoped Real SchwartzMap
open Complex MeasureTheory

namespace GaloisForLFunctions

noncomputable section

/-- The translated Gaussian `e^{-π(x-y)²}`. -/
def coherentGauss (y : ℝ) : 𝓢(ℝ, ℂ) := SchwartzMap.compSubConstCLM ℂ y gaussianSchwartz

@[simp] theorem coherentGauss_apply (y x : ℝ) : coherentGauss y x = (gaussReal (x - y) : ℂ) := rfl

/-- **The translated Gaussian is an eigenvector of the annihilation operator.** -/
theorem annihilationCLM_coherentGauss (y : ℝ) :
    annihilationCLM (coherentGauss y) = ((2 * π * y : ℝ) : ℂ) • coherentGauss y := by
  apply SchwartzMap.ext
  intro x
  have hr : HasDerivAt (fun t : ℝ => ((gaussReal (t - y) : ℝ) : ℂ))
      (((-(2 * π * (x - y)) * gaussReal (x - y) : ℝ) : ℂ)) x := by
    have h := (hasDerivAt_gaussReal (x - y)).comp x ((hasDerivAt_id x).sub_const y)
    simpa using h.ofReal_comp
  have hc : deriv (coherentGauss y : ℝ → ℂ) x =
      ((-(2 * π * (x - y)) * gaussReal (x - y) : ℝ) : ℂ) := hr.deriv
  rw [annihilationCLM_apply, hc, smul_apply, coherentGauss_apply, smul_eq_mul]
  push_cast
  ring

/-- The bilinear pairings with the Hermite functions form a geometric sequence. -/
theorem schwartzPair_coherentGauss_hermiteSchwartz (y : ℝ) (n : ℕ) :
    schwartzPair (coherentGauss y) (hermiteSchwartz n) =
      (y : ℂ) ^ n * schwartzPair (coherentGauss y) (hermiteSchwartz 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : schwartzPair (coherentGauss y) (creationCLM (hermiteSchwartz n)) =
        (2 * (π : ℂ)) * schwartzPair (coherentGauss y) (hermiteSchwartz (n + 1)) := by
      rw [creationCLM_hermiteSchwartz, schwartzPair_smul_right]
    have h2 : schwartzPair (coherentGauss y) (creationCLM (hermiteSchwartz n)) =
        ((2 * π * y : ℝ) : ℂ) * schwartzPair (coherentGauss y) (hermiteSchwartz n) := by
      rw [schwartzPair_comm, schwartzPair_creationCLM, annihilationCLM_coherentGauss,
        schwartzPair_smul_right, schwartzPair_comm]
    have hπ : (2 * (π : ℂ)) ≠ 0 := two_pi_ne_zero
    rw [h2, ih] at h1
    rw [pow_succ]
    apply mul_left_cancel₀ hπ
    rw [← h1]
    push_cast
    ring

theorem norm_sq_toLp_hermiteSchwartz (n : ℕ) :
    ‖(hermiteSchwartz n).toLp 2 (volume : Measure ℝ)‖ ^ 2 =
      (n.factorial : ℝ) / π ^ n * ‖(hermiteSchwartz 0).toLp 2 (volume : Measure ℝ)‖ ^ 2 := by
  have hself : ∀ m : ℕ, ((‖(hermiteSchwartz m).toLp 2 (volume : Measure ℝ)‖ ^ 2 : ℝ) : ℂ) =
      schwartzPair (hermiteSchwartz m) (hermiteSchwartz m) := fun m => by
    rw [← inner_hermiteSchwartz_toLp, inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  have hπ : (0 : ℝ) < π := Real.pi_pos
  induction n with
  | zero => simp
  | succ n ih =>
    have h := schwartzPair_hermiteSchwartz_succ_self n
    rw [← hself, ← hself] at h
    have hR : ‖(hermiteSchwartz (n + 1)).toLp 2 (volume : Measure ℝ)‖ ^ 2 =
        ((n : ℝ) + 1) / π * ‖(hermiteSchwartz n).toLp 2 (volume : Measure ℝ)‖ ^ 2 := by
      exact_mod_cast h
    rw [hR, ih, Nat.factorial_succ, pow_succ]
    push_cast
    field_simp
    ring

theorem norm_toLp_hermiteSchwartz_pos (n : ℕ) :
    0 < ‖(hermiteSchwartz n).toLp 2 (volume : Measure ℝ)‖ := by
  refine (norm_nonneg _).lt_of_ne fun h => ?_
  have h1 := norm_toLp_hermiteUnit n
  rw [hermiteUnit, ← h, Complex.ofReal_zero, inv_zero, zero_smul] at h1
  have h2 : ‖(0 : 𝓢(ℝ, ℂ)).toLp 2 (volume : Measure ℝ)‖ = 0 := by
    rw [show (0 : 𝓢(ℝ, ℂ)).toLp 2 (volume : Measure ℝ) = 0 from
      (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ)).map_zero, norm_zero]
  rw [h2] at h1
  exact zero_ne_one h1

/-- **The Poisson law of the Hermite energy.** -/
theorem norm_sq_hermiteCoeff_coherentGauss (y : ℝ) (n : ℕ) :
    ‖hermiteCoeff (coherentGauss y) n‖ ^ 2 =
      ‖hermiteCoeff (coherentGauss y) 0‖ ^ 2 * ((π * y ^ 2) ^ n / n.factorial) := by
  have hn := norm_toLp_hermiteSchwartz_pos n
  have h0 := norm_toLp_hermiteSchwartz_pos 0
  have hN := norm_sq_toLp_hermiteSchwartz n
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  rw [hermiteCoeff, hermiteCoeff, schwartzPair_coherentGauss_hermiteSchwartz, norm_mul, norm_mul,
    norm_mul, norm_inv, norm_inv, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hn.le,
    Real.norm_of_nonneg h0.le, norm_pow, Complex.norm_real, Real.norm_eq_abs, mul_pow, mul_pow,
    mul_pow, inv_pow, inv_pow, hN, ← pow_mul, mul_comm n 2, pow_mul, sq_abs]
  field_simp
  ring

/-! ## Parseval -/

/-- **Parseval for an orthonormal expansion.** -/
theorem hasSum_norm_sq_of_hasSum_orthonormal {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {e : ℕ → E} (he : Orthonormal ℂ e) {d : ℕ → ℂ} {G : E}
    (h : HasSum (fun j => d j • e j) G) : HasSum (fun j => ‖d j‖ ^ 2) (‖G‖ ^ 2) := by
  have hk : ∀ k, inner ℂ (e k) G = d k := fun k => by
    have h1 := h.mapL (innerSL ℂ (e k))
    have h2 : HasSum (fun j => (innerSL ℂ (e k)) (d j • e j)) (d k) := by
      have : (fun j => (innerSL ℂ (e k)) (d j • e j)) = fun j => if j = k then d k else 0 := by
        funext j
        rw [innerSL_apply_apply, inner_smul_right, orthonormal_iff_ite.1 he k j]
        by_cases hjk : j = k
        · subst hjk; simp
        · rw [if_neg (Ne.symm hjk), if_neg hjk, mul_zero]
      rw [this]
      exact hasSum_ite_eq k (d k)
    rw [innerSL_apply_apply] at h1
    exact h1.unique h2
  have hG := h.mapL (innerSL ℂ G)
  have hfun : (fun j => (innerSL ℂ G) (d j • e j)) = fun j => ((‖d j‖ ^ 2 : ℝ) : ℂ) := by
    funext j
    rw [innerSL_apply_apply, inner_smul_right, ← inner_conj_symm, hk, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
  rw [hfun, innerSL_apply_apply, inner_self_eq_norm_sq_to_K] at hG
  have hG' : HasSum (fun j => ((‖d j‖ ^ 2 : ℝ) : ℂ)) ((‖G‖ ^ 2 : ℝ) : ℂ) := by
    push_cast at hG ⊢; exact hG
  exact Complex.hasSum_ofReal.1 hG'

theorem orthonormal_hermiteUnit_toLp :
    Orthonormal ℂ (fun j : ℕ => (hermiteUnit j).toLp 2 (volume : Measure ℝ)) := by
  convert orthonormal_hermiteSchwartz_toLp using 1
  funext n
  rw [hermiteUnit]
  exact (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ)).map_smul _ _

/-- **Parseval for the Hermite expansion.** -/
theorem hasSum_norm_sq_hermiteCoeff (f : 𝓢(ℝ, ℂ)) :
    HasSum (fun j => ‖hermiteCoeff f j‖ ^ 2) (‖f.toLp 2 (volume : Measure ℝ)‖ ^ 2) :=
  hasSum_norm_sq_of_hasSum_orthonormal orthonormal_hermiteUnit_toLp
    (hasSum_hermiteExpansion_toLp f)

/-- The truncation `Π_N f = Σ_{j<N} c_j(f) ĥ_j`. -/
def hermiteTrunc (f : 𝓢(ℝ, ℂ)) (N : ℕ) : 𝓢(ℝ, ℂ) :=
  ∑ j ∈ Finset.range N, hermiteCoeff f j • hermiteUnit j

/-- **Tail Parseval.**  `‖f − Π_N f‖² = Σ_{j ≥ N} |c_j(f)|²`. -/
theorem hasSum_norm_sq_hermiteCoeff_tail (f : 𝓢(ℝ, ℂ)) (N : ℕ) :
    HasSum (fun i => ‖hermiteCoeff f (i + N)‖ ^ 2)
      (‖(f - hermiteTrunc f N).toLp 2 (volume : Measure ℝ)‖ ^ 2) := by
  have hexp := (hasSum_nat_add_iff' N).2 (hasSum_hermiteExpansion_toLp f)
  have heq : (f - hermiteTrunc f N).toLp 2 (volume : Measure ℝ) =
      f.toLp 2 (volume : Measure ℝ) - ∑ i ∈ Finset.range N,
        hermiteCoeff f i • (hermiteUnit i).toLp 2 (volume : Measure ℝ) := by
    rw [hermiteTrunc]
    have h1 := (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ)).map_sub f
      (∑ j ∈ Finset.range N, hermiteCoeff f j • hermiteUnit j)
    rw [map_sum] at h1
    simp only [map_smul, SchwartzMap.toLpCLM_apply] at h1
    exact h1
  rw [heq]
  exact hasSum_norm_sq_of_hasSum_orthonormal
    (orthonormal_hermiteUnit_toLp.comp (fun i => i + N) (add_left_injective N)) hexp

/-! ## The Poisson tail of a translated Gaussian -/

/-- `|c_0(ψ_y)|² = ‖ψ_y‖² e^{-πy²}`. -/
theorem norm_sq_hermiteCoeff_coherentGauss_zero (y : ℝ) :
    ‖hermiteCoeff (coherentGauss y) 0‖ ^ 2 =
      ‖(coherentGauss y).toLp 2 (volume : Measure ℝ)‖ ^ 2 * Real.exp (-(π * y ^ 2)) := by
  have hP := hasSum_norm_sq_hermiteCoeff (coherentGauss y)
  have hexp : HasSum (fun n : ℕ => ‖hermiteCoeff (coherentGauss y) 0‖ ^ 2 *
      ((π * y ^ 2) ^ n / n.factorial)) (‖hermiteCoeff (coherentGauss y) 0‖ ^ 2 *
        Real.exp (π * y ^ 2)) := by
    have := NormedSpace.expSeries_div_hasSum_exp (π * y ^ 2)
    rw [← Real.exp_eq_exp_ℝ] at this
    exact this.mul_left _
  have hfun : (fun j => ‖hermiteCoeff (coherentGauss y) j‖ ^ 2) = fun n : ℕ =>
      ‖hermiteCoeff (coherentGauss y) 0‖ ^ 2 * ((π * y ^ 2) ^ n / n.factorial) :=
    funext (norm_sq_hermiteCoeff_coherentGauss y)
  rw [hfun] at hP
  have heq := hP.unique hexp
  rw [heq, mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

/-- **The Poisson tail.**  `‖ψ_y − Π_N ψ_y‖² = ‖ψ_y‖² e^{-λ} Σ_{j ≥ N} λʲ/j!`, `λ = πy²`. -/
theorem hasSum_tail_coherentGauss (y : ℝ) (N : ℕ) :
    HasSum (fun i => ‖(coherentGauss y).toLp 2 (volume : Measure ℝ)‖ ^ 2 *
      Real.exp (-(π * y ^ 2)) * ((π * y ^ 2) ^ (i + N) / (i + N).factorial))
      (‖(coherentGauss y - hermiteTrunc (coherentGauss y) N).toLp 2 (volume : Measure ℝ)‖ ^ 2) := by
  have h := hasSum_norm_sq_hermiteCoeff_tail (coherentGauss y) N
  convert h using 2 with i
  rw [norm_sq_hermiteCoeff_coherentGauss, norm_sq_hermiteCoeff_coherentGauss_zero]

/-- `μ^m e^{-μ}` is increasing on `[0, m]`. -/
theorem pow_mul_exp_neg_le_of_le_of_le {l μ : ℝ} {m : ℕ} (hl : 0 ≤ l) (hlμ : l ≤ μ) (hμm : μ ≤ m) :
    l ^ m * Real.exp (-l) ≤ μ ^ m * Real.exp (-μ) := by
  rcases hl.eq_or_lt with rfl | hl0
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp only [pow_zero, one_mul, neg_zero, Real.exp_zero]
      exact Real.one_le_exp (by push_cast at hμm; linarith)
    · rw [zero_pow hm.ne', zero_mul]; positivity
  have hμ0 : 0 < μ := lt_of_lt_of_le hl0 hlμ
  set t := l / μ with ht
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 := by rw [ht, div_le_one hμ0]; exact hlμ
  have hl' : l = t * μ := by rw [ht]; field_simp
  have h1 : t ^ m ≤ Real.exp (m * (t - 1)) := by
    have := Real.add_one_le_exp (t - 1)
    calc t ^ m ≤ Real.exp (t - 1) ^ m := pow_le_pow_left₀ ht0 (by linarith) m
      _ = Real.exp (m * (t - 1)) := by rw [← Real.exp_nat_mul]
  have h2 : Real.exp (m * (t - 1)) ≤ Real.exp (μ * (t - 1)) :=
    Real.exp_le_exp.2 (by nlinarith)
  rw [hl', mul_pow]
  calc t ^ m * μ ^ m * Real.exp (-(t * μ)) ≤ Real.exp (μ * (t - 1)) * μ ^ m * Real.exp (-(t * μ)) := by
        gcongr; exact h1.trans h2
    _ = μ ^ m * Real.exp (-μ) := by
        rw [mul_comm (Real.exp _) (μ ^ m), mul_assoc, ← Real.exp_add]; congr 2; ring

/-- **Sharp Poisson tail.**  If `0 ≤ λ ≤ θN` with `0 ≤ θ < 1`, then
`e^{-λ} Σ_{j ≥ N} λʲ/j! ≤ (θ e^{1-θ})^N/(1 − θ)`. -/
theorem exp_neg_mul_tsum_tail_le {l θ : ℝ} {N : ℕ} (hl : 0 ≤ l) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hlN : l ≤ θ * N) :
    Real.exp (-l) * ∑' i : ℕ, l ^ (i + N) / (i + N).factorial ≤
      (θ * Real.exp (1 - θ)) ^ N / (1 - θ) := by
  have h1θ : 0 < 1 - θ := by linarith
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have hl0 : l = 0 := by simp at hlN; linarith
    subst hl0
    have : (∑' i : ℕ, (0 : ℝ) ^ (i + 0) / (i + 0).factorial) = 1 := by
      rw [tsum_eq_single 0 (fun i hi => by simp [hi])]
      simp
    rw [this]
    simp only [neg_zero, Real.exp_zero, one_mul, pow_zero]
    rw [le_div_iff₀ h1θ]; linarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  -- term bound
  have hterm : ∀ i : ℕ, l ^ (i + N) / (i + N).factorial ≤ l ^ N / N.factorial * θ ^ i := by
    intro i
    have hfac : (N.factorial : ℝ) * (N : ℝ) ^ i ≤ (i + N).factorial := by
      have h1 := Nat.factorial_mul_pow_le_factorial (m := N) (n := i)
      have h2 : (N.factorial : ℝ) * ((N : ℝ) + 1) ^ i ≤ (N + i).factorial := by exact_mod_cast h1
      have h3 : (N : ℝ) ^ i ≤ ((N : ℝ) + 1) ^ i := pow_le_pow_left₀ (by positivity) (by linarith) i
      rw [add_comm]
      calc (N.factorial : ℝ) * (N : ℝ) ^ i ≤ N.factorial * ((N : ℝ) + 1) ^ i := by gcongr
        _ ≤ _ := h2
    have hli : l ^ i ≤ (θ * N) ^ i := pow_le_pow_left₀ hl hlN i
    rw [pow_add, div_le_iff₀ (by positivity)]
    calc l ^ i * l ^ N ≤ (θ * N) ^ i * l ^ N := by gcongr
      _ = l ^ N / N.factorial * θ ^ i * (N.factorial * (N : ℝ) ^ i) := by
          field_simp; ring
      _ ≤ l ^ N / N.factorial * θ ^ i * (i + N).factorial := by gcongr
  have hgeom : HasSum (fun i : ℕ => l ^ N / N.factorial * θ ^ i) (l ^ N / N.factorial / (1 - θ)) := by
    have := (hasSum_geometric_of_lt_one hθ0 hθ1).mul_left (l ^ N / N.factorial)
    simpa [div_eq_mul_inv] using this
  have hsumm : Summable (fun i : ℕ => l ^ (i + N) / (i + N).factorial) :=
    hgeom.summable.of_nonneg_of_le (fun i => by positivity) hterm
  have htsum : ∑' i : ℕ, l ^ (i + N) / (i + N).factorial ≤ l ^ N / N.factorial / (1 - θ) :=
    (hsumm.tsum_le_tsum hterm hgeom.summable).trans (le_of_eq hgeom.tsum_eq)
  -- `l^N e^{-l}/N! ≤ (θ e^{1-θ})^N`
  have hmono := pow_mul_exp_neg_le_of_le_of_le hl hlN (by nlinarith)
  have hfacN : (N : ℝ) ^ N / N.factorial ≤ Real.exp N := Real.pow_div_factorial_le_exp _ hNpos.le N
  have hkey : Real.exp (-l) * (l ^ N / N.factorial) ≤ (θ * Real.exp (1 - θ)) ^ N := by
    have e1 : (θ * Real.exp (1 - θ)) ^ N = (θ * N) ^ N * Real.exp (-(θ * N)) *
        (Real.exp N / (N : ℝ) ^ N) := by
      rw [mul_pow, mul_pow, ← Real.exp_nat_mul]
      field_simp
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    rw [e1]
    have hNN : 0 < (N : ℝ) ^ N := by positivity
    have hfac' : 1 / (N.factorial : ℝ) ≤ Real.exp N / (N : ℝ) ^ N := by
      rw [div_le_div_iff₀ (by positivity) hNN]
      rw [div_le_iff₀ (by positivity)] at hfacN
      linarith
    calc Real.exp (-l) * (l ^ N / N.factorial) = l ^ N * Real.exp (-l) * (1 / N.factorial) := by
          ring
      _ ≤ (θ * N) ^ N * Real.exp (-(θ * N)) * (Real.exp N / (N : ℝ) ^ N) := by
          gcongr
  calc Real.exp (-l) * ∑' i : ℕ, l ^ (i + N) / (i + N).factorial
      ≤ Real.exp (-l) * (l ^ N / N.factorial / (1 - θ)) :=
        mul_le_mul_of_nonneg_left htsum (Real.exp_pos _).le
    _ = Real.exp (-l) * (l ^ N / N.factorial) / (1 - θ) := by ring
    _ ≤ (θ * Real.exp (1 - θ)) ^ N / (1 - θ) := by gcongr

theorem mul_exp_one_sub_lt_one {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) : θ * Real.exp (1 - θ) < 1 := by
  rcases hθ0.eq_or_lt with rfl | hpos
  · simp
  have h := Real.add_one_lt_exp (show θ - 1 ≠ 0 by linarith)
  have h2 : Real.exp (1 - θ) * Real.exp (θ - 1) = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos (1 - θ)]

end

end GaloisForLFunctions
