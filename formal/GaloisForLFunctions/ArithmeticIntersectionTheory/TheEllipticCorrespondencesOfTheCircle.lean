import GaloisForLFunctions.ArithmeticIntersectionTheory.GaussDigammaIsTheFourierTransformOfTheTorsionEnergy

/-!
# The elliptic correspondences of the circle

Besides the power maps `[t] : z ↦ z^t` (Hecke, hyperbolic on the zero side), the characteristic
circle carries the **rotations** `R_ζ : z ↦ ζ z` by roots of unity, correspondences of finite order:
elliptic. Together they form the affine semigroup `z ↦ ζ z^t`, with the Baumslag–Solitar relation
`[t] ∘ R_ζ = R_{ζ^t} ∘ [t]` (`pow_mul_rotate`).

* **Rotations are exact** (`circleKernel_rotate`): the Abel pairing is rotation invariant, with no
  anomaly — unlike the power maps, which move the regulator.
* **Archimedean Hodge index on point cycles** (`hasSum_pointEnergy`): for any finite cycle
  `Σ x_a δ_{e^{iθ_a}}` on the circle, its energy is `Σ_{j ≥ 1} (r^j/j)(C_j² + S_j²)` with
  `C_j = Σ x_a cos(jθ_a)`, `S_j = Σ x_a sin(jθ_a)`: rotation characters diagonalize the pairing and every
  frequency carries a nonnegative weight.
* **The rotation spectrum on `μ_N` is archimedean** (`pointEnergy_rootCycle_eq`): on the torsion
  `μ_N` the frequencies fold modulo `N`, and the eigenvalue of the rotation mode `k` is the lattice
  germ `(r^k/N) G_{r^N}(k/N)`, `0 < k < N`, the zero mode carrying `−log(1 − r^N)/N`. By Gauss's
  digamma theorem (`gauss_digamma_theorem`) the renormalized eigenvalues are `−(ψ(k/N) + γ + log N)/N`:
  values of the archimedean local factor at rational points.

So the elliptic structure of the circle localizes in the additive variable `k/N ∈ ℚ/ℤ`, and its
spectrum is the archimedean factor; the zeros of `ζ` do not appear in it. They appear only through
the Hecke correspondences gluing the levels `N` (Weil's prime kernel on orbit cycles). An elliptic
localizer for zeros cannot come from rotations of the torsion: their dual variable is the wrong one.
-/

noncomputable section

open Finset Filter Topology Complex
open scoped Real ComplexConjugate

namespace GaloisForLFunctions.ArithmeticIntersectionTheory

open ArithmeticEffectivityTheory RenormalizedBiarithmeticGeometry

/-- **Rotations are exact**: `k_r(ζz, ζw) = k_r(z, w)` for `|ζ| = 1`. -/
theorem circleKernel_rotate (r : ℝ) {ζ : ℂ} (hζ : ‖ζ‖ = 1) (z w : ℂ) :
    circleKernel r (ζ * z) (ζ * w) = circleKernel r z w := by
  have h : ζ * conj ζ = 1 := by
    rw [mul_conj, normSq_eq_norm_sq, hζ]; simp
  simp only [circleKernel, map_mul]
  rw [show ζ * z * (conj ζ * conj w) = z * conj w by
    calc ζ * z * (conj ζ * conj w) = (ζ * conj ζ) * (z * conj w) := by ring
      _ = z * conj w := by rw [h, one_mul]]

/-- **The Baumslag–Solitar relation** `[t] ∘ R_ζ = R_{ζ^t} ∘ [t]`. -/
theorem pow_mul_rotate (ζ z : ℂ) (t : ℕ) : (ζ * z) ^ t = ζ ^ t * z ^ t := mul_pow ζ z t

/-! ### Point cycles: rotation characters diagonalize the pairing -/

variable {ι : Type*}

/-- The cosine coefficient `C_j = Σ_a x_a cos(jθ_a)` of a point cycle. -/
def cosCoeff (s : Finset ι) (θ : ι → ℝ) (x : ι → ℝ) (j : ℕ) : ℝ :=
  ∑ a ∈ s, x a * Real.cos (j * θ a)

/-- The sine coefficient `S_j = Σ_a x_a sin(jθ_a)` of a point cycle. -/
def sinCoeff (s : Finset ι) (θ : ι → ℝ) (x : ι → ℝ) (j : ℕ) : ℝ :=
  ∑ a ∈ s, x a * Real.sin (j * θ a)

/-- The point `e^{iθ}` of the circle. -/
def circlePoint (θ : ℝ) : ℂ := exp ((θ : ℂ) * I)

theorem norm_circlePoint (θ : ℝ) : ‖circlePoint θ‖ = 1 := norm_exp_ofReal_mul_I θ

theorem re_circlePoint_mul_conj_pow (θ φ : ℝ) (j : ℕ) :
    ((circlePoint θ * conj (circlePoint φ)) ^ j).re =
      Real.cos (j * θ) * Real.cos (j * φ) + Real.sin (j * θ) * Real.sin (j * φ) := by
  have h : circlePoint θ * conj (circlePoint φ) = exp (((θ - φ : ℝ) : ℂ) * I) := by
    rw [circlePoint, circlePoint, ← exp_conj, map_mul, conj_ofReal, conj_I, ← exp_add]
    congr 1; push_cast; ring
  rw [h, ← exp_nat_mul, ← mul_assoc, ← ofReal_natCast, ← ofReal_mul, exp_ofReal_mul_I_re,
    show (j : ℝ) * (θ - φ) = j * θ - j * φ by ring, Real.cos_sub]

/-- **Archimedean Hodge index on point cycles.** The Abel energy of `Σ x_a δ_{e^{iθ_a}}` is
`Σ_j (r^j/j)(C_j² + S_j²)`. -/
theorem hasSum_pointEnergy {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (s : Finset ι) (θ : ι → ℝ)
    (x : ι → ℝ) :
    HasSum (fun j : ℕ => r ^ j / j * (cosCoeff s θ x j ^ 2 + sinCoeff s θ x j ^ 2))
      (∑ a ∈ s, ∑ b ∈ s, x a * x b * circleKernel r (circlePoint (θ a)) (circlePoint (θ b))) := by
  have h : ∀ a ∈ s, ∀ b ∈ s, HasSum (fun j : ℕ => x a * x b * (r ^ j / j *
      (Real.cos (j * θ a) * Real.cos (j * θ b) + Real.sin (j * θ a) * Real.sin (j * θ b))))
      (x a * x b * circleKernel r (circlePoint (θ a)) (circlePoint (θ b))) := by
    intro a _ b _
    have hw : ‖circlePoint (θ a) * conj (circlePoint (θ b))‖ ≤ 1 := by
      rw [norm_mul, RCLike.norm_conj, norm_circlePoint, norm_circlePoint, one_mul]
    have := (hasSum_neg_log_norm_one_sub hr0 hr1 hw).mul_left (x a * x b)
    simpa only [re_circlePoint_mul_conj_pow, circleKernel] using this
  have hall := hasSum_sum fun a ha => hasSum_sum fun b hb => h a ha b hb
  convert hall using 1
  funext j
  simp only [cosCoeff, sinCoeff, sq, sum_mul_sum]
  rw [← sum_add_distrib, mul_sum]
  refine sum_congr rfl fun a _ => ?_
  rw [← sum_add_distrib, mul_sum]
  refine sum_congr rfl fun b _ => ?_
  ring

/-! ### The torsion `μ_N`: folding the frequencies -/

/-- The point cycle `Σ_{a < N} x_a δ_{ζ_N^a}` on `μ_N`. -/
def rootCycleEnergy (r : ℝ) (N : ℕ) (x : ℕ → ℝ) : ℝ :=
  ∑ a ∈ range N, ∑ b ∈ range N, x a * x b *
    circleKernel r (circlePoint (rootAngle N a)) (circlePoint (rootAngle N b))

theorem cos_rootAngle_add (N j a : ℕ) (hN : 0 < N) :
    Real.cos (((j + N : ℕ) : ℝ) * rootAngle N a) = Real.cos (j * rootAngle N a) := by
  have : ((j + N : ℕ) : ℝ) * rootAngle N a = j * rootAngle N a + a * (2 * π) := by
    rw [rootAngle]; push_cast; field_simp
  rw [this, Real.cos_add_nat_mul_two_pi]

theorem sin_rootAngle_add (N j a : ℕ) (hN : 0 < N) :
    Real.sin (((j + N : ℕ) : ℝ) * rootAngle N a) = Real.sin (j * rootAngle N a) := by
  have : ((j + N : ℕ) : ℝ) * rootAngle N a = j * rootAngle N a + a * (2 * π) := by
    rw [rootAngle]; push_cast; field_simp
  rw [this, Real.sin_add_nat_mul_two_pi]

/-- The squared mode `C_j² + S_j²` of a cycle on `μ_N` depends on `j mod N`. -/
def rootMode (N : ℕ) (x : ℕ → ℝ) (j : ℕ) : ℝ :=
  cosCoeff (range N) (rootAngle N) x j ^ 2 + sinCoeff (range N) (rootAngle N) x j ^ 2

theorem rootMode_add (N : ℕ) (hN : 0 < N) (x : ℕ → ℝ) (j : ℕ) :
    rootMode N x (j + N) = rootMode N x j := by
  simp only [rootMode, cosCoeff, sinCoeff, cos_rootAngle_add N j _ hN, sin_rootAngle_add N j _ hN]

theorem rootMode_mod (N : ℕ) (hN : 0 < N) (x : ℕ → ℝ) (j : ℕ) :
    rootMode N x j = rootMode N x (j % N) := by
  conv_lhs => rw [← Nat.mod_add_div j N]
  induction j / N with
  | zero => simp
  | succ m ih => rw [Nat.mul_succ, ← add_assoc, rootMode_add N hN, ih]

/-- The frequencies of a residue class: `Σ_{j ≡ c} r^j/j`, as a lattice germ for `0 < c < N`. -/
theorem hasSum_residue {N c : ℕ} (hc : 0 < c) (hcN : c < N) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun j : ℕ => r ^ j / j * (if j % N = c then 1 else 0))
      (r ^ c / N * latticeGerm (r ^ N) ((c : ℝ) / N)) := by
  have hN : 0 < N := hc.trans hcN
  convert hasSum_progression hN hc hcN hr0 hr1 using 3 with j
  congr 1
  apply propext
  constructor
  · intro h
    refine ⟨j / N + 1, ?_⟩
    have := Nat.mod_add_div j N
    have hsub : N - c + c = N := Nat.sub_add_cancel hcN.le
    rw [h] at this
    nlinarith [this, hsub]
  · rintro ⟨d, hd⟩
    have h1 : (j + (N - c)) % N = 0 := by rw [hd, Nat.mul_mod_right]
    have h2 : (j + (N - c)) % N = (j % N + (N - c)) % N := by
      rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : N - c < N)]
    rw [h2] at h1
    have hj : j % N < N := Nat.mod_lt j hN
    rcases Nat.lt_or_ge (j % N + (N - c)) N with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt] at h1; omega
    · have : (j % N + (N - c)) % N = j % N + (N - c) - N := by
        rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
      omega

/-- The zero mode: `Σ_{N ∣ j} r^j/j = −log(1 − r^N)/N`. -/
theorem hasSum_residue_zero {N : ℕ} (hN : 0 < N) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun j : ℕ => r ^ j / j * (if j % N = 0 then 1 else 0))
      (-Real.log (1 - r ^ N) / N) := by
  set g : ℕ → ℕ := fun m => (m + 1) * N
  have hg : Function.Injective g := fun m m' h => by
    simp only [g] at h; exact Nat.succ_injective (Nat.eq_of_mul_eq_mul_right hN h)
  have hsupp : ∀ j ∉ Set.range g, r ^ j / j * (if j % N = 0 then 1 else 0) = 0 := by
    intro j hj
    by_cases hj0 : j = 0
    · simp [hj0]
    rw [if_neg, mul_zero]
    intro h
    apply hj
    refine ⟨j / N - 1, ?_⟩
    have hpos : 0 < j / N := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hj0)
      (Nat.dvd_of_mod_eq_zero h)) hN
    simp only [g]
    rw [Nat.sub_add_cancel hpos, Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h)]
  rw [← hg.hasSum_iff hsupp]
  have hrN0 : 0 ≤ r ^ N := pow_nonneg hr0 N
  have hrN1 : r ^ N < 1 := pow_lt_one₀ hr0 hr1 hN.ne'
  have hlog := Real.hasSum_pow_div_log_of_abs_lt_one (show |r ^ N| < 1 by
    rw [abs_of_nonneg hrN0]; exact hrN1)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have e : (fun j : ℕ => r ^ j / j * (if j % N = 0 then 1 else 0)) ∘ g =
      fun m : ℕ => (r ^ N) ^ (m + 1) / ((m : ℝ) + 1) / N := by
    funext m
    simp only [Function.comp_def, g, Nat.mul_mod_left, if_true, mul_one]
    push_cast
    rw [← pow_mul, mul_comm N (m + 1)]
    field_simp
  rw [e]
  exact hlog.div_const (N : ℝ)

/-- **The rotation spectrum of the torsion energy on `μ_N`.** For `0 ≤ r < 1`, the energy of the
cycle `Σ_{a<N} x_a δ_{ζ_N^a}` is
`(−log(1 − r^N)/N) · mode₀ + Σ_{0<k<N} (r^k/N) G_{r^N}(k/N) · mode_k`,
`mode_k = C_k² + S_k²`: the rotation modes diagonalize it, with lattice-germ eigenvalues. -/
theorem rootCycleEnergy_eq {N : ℕ} (hN : 0 < N) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (x : ℕ → ℝ) :
    rootCycleEnergy r N x = -Real.log (1 - r ^ N) / N * rootMode N x 0 +
      ∑ k ∈ Ico 1 N, r ^ k / N * latticeGerm (r ^ N) ((k : ℝ) / N) * rootMode N x k := by
  have hser := hasSum_pointEnergy hr0 hr1 (range N) (rootAngle N) x
  -- fold every frequency onto its residue
  have hfold : ∀ j : ℕ, r ^ j / j * (cosCoeff (range N) (rootAngle N) x j ^ 2 +
      sinCoeff (range N) (rootAngle N) x j ^ 2) =
      ∑ k ∈ range N, r ^ j / j * (if j % N = k then 1 else 0) * rootMode N x k := by
    intro j
    rw [sum_eq_single (j % N)]
    · rw [if_pos rfl, mul_one, ← rootMode_mod N hN x j]; rfl
    · intro k _ hk; rw [if_neg (Ne.symm hk)]; ring
    · intro h; exact absurd (mem_range.mpr (Nat.mod_lt j hN)) h
  simp only [hfold] at hser
  have hparts : HasSum (fun j : ℕ => ∑ k ∈ range N, r ^ j / j * (if j % N = k then 1 else 0) *
      rootMode N x k) (∑ k ∈ range N, (if k = 0 then -Real.log (1 - r ^ N) / N else
        r ^ k / N * latticeGerm (r ^ N) ((k : ℝ) / N)) * rootMode N x k) := by
    refine hasSum_sum fun k hk => ?_
    split_ifs with h0
    · subst h0; exact (hasSum_residue_zero hN hr0 hr1).mul_right _
    · exact (hasSum_residue (Nat.pos_of_ne_zero h0) (mem_range.mp hk) hr0 hr1).mul_right _
  rw [rootCycleEnergy, hser.unique hparts, range_eq_Ico, sum_eq_sum_Ico_succ_bot hN, if_pos rfl]
  congr 1
  refine sum_congr rfl fun k hk => ?_
  rw [if_neg (by simp at hk; omega)]

/-- The eigenvalues of the rotation modes are nonnegative at every regulator: the archimedean Hodge
index on `μ_N`. -/
theorem rootCycle_eigenvalues_nonneg {N k : ℕ} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hk : 0 < k)
    (hN : 0 < N) :
    0 ≤ r ^ k / N * latticeGerm (r ^ N) ((k : ℝ) / N) := by
  have hz : (0 : ℝ) < (k : ℝ) / N := by positivity
  refine mul_nonneg (by positivity) ?_
  exact (hasSum_latticeGerm (pow_nonneg hr0 N) (pow_lt_one₀ hr0 hr1 hN.ne') hz).nonneg
    fun m => div_nonneg (pow_nonneg (pow_nonneg hr0 N) m) (by positivity)

end GaloisForLFunctions.ArithmeticIntersectionTheory
