import GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies.ShortColumnsAreIncoherent
import GaloisForLFunctions.MetaplecticMobiusDescent.QuadraticTraceCoordinates
import GaloisForLFunctions.FamilyContinuationTheory.TheGaussSumOfAPrimePowerLivesOnOneLayer

/-!
# Short columns of the Eisenstein lattice are incoherent

The rows of the cubic-theta probe are elements `n = x + yω` of `O = ℤ[ω]`, i.e. points `(x, y)` of
`ℤ²`. A column of modulus `c` is a function `φ` of `n mod c`. Finite Fourier analysis on `O/(c)`
with the primitive trace character `ψ_c` writes it as
`|O/(c)| φ(n) = Σ_{h mod c} φ̂(h) ψ_c(hn)`, `φ̂(h) = Σ_d φ(d) ψ_c(−hd)` (`card_mul_eq_sum_dual`).

In coordinates `ψ_c(hn)` is the lattice phase `e(⟨(x, y), θ_h⟩)` with
`θ_h = ((aq − bp)/N, (ap − aq + bq)/N)` for `c = a + bω`, `h = p + qω`, `N = a² − ab + b²`
(`traceChar_mul_eval_eq_phase`). The dual frequencies sit far from the lattice
(`sqrt_le_norm_sub_thetaH`): if `c ∤ h`, then `‖m − θ_h‖² ≥ 2/(3N)` for every `m ∈ ℤ²`. The
integers `r, s` with `N(θ_h − m) = (r, s)` are the coordinates of `c̄·(h − c·o)` under the perfect
trace pairing, so `r² + s² ≥ ⅔ N(c̄(h − co)) = ⅔ N·N(h − co) ≥ ⅔ N`; the inequality is
`T² + (S − T)² − ⅔(S² − ST + T²) = ⅓(S − 2T)²`.

With the Poisson tool of `ShortColumnsAreIncoherent` (`norm_tsum_eisensteinColumn_le`): for a
column of mean zero and rows weighted by `f(Bn)` with `‖B^{−*}v‖ ≥ μ‖v‖`, the row sum is at most
`|det B|⁻¹ · K · (μ √(2/(3N)))^{−M} · |O/(c)|⁻¹ Σ_h |φ̂(h)|`. For rows of norm `≍ U`
(`B = U^{−1/2}B₀`, `μ ≍ U^{1/2}`) this is negligible as soon as `N(c) ≤ U^{1−ε}`: a column of norm
below the row norm is incoherent to every order, which is the sharp range.
-/

noncomputable section

open scoped BigOperators Classical FourierTransform

namespace GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies

open HTGeometry HTGeometry.IntegerLatticePoisson MetaplecticMobiusDescent
  MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.Eisenstein.Coordinates
  FamilyContinuationTheory

local notation "E" => EuclideanSpace ℝ (Fin 2)
local notation "Z" => Fin 2 → ℤ

/-! ### Finite Fourier inversion on a residue ring -/

/-- **Fourier inversion with a primitive additive character.** On a finite commutative ring with
a primitive character `ψ`, `|R| φ(z) = Σ_h φ̂(h) ψ(hz)` with `φ̂(h) = Σ_d φ(d) ψ(−hd)`. -/
theorem card_mul_eq_sum_dual {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
    {ψ : AddChar R ℂ} (hψ : ψ.IsPrimitive) (φ : R → ℂ) (z : R) :
    (Fintype.card R : ℂ) * φ z =
      ∑ h : R, (∑ d : R, φ d * ψ (-(h * d))) * ψ (h * z) := by
  have hswap : ∑ h : R, (∑ d : R, φ d * ψ (-(h * d))) * ψ (h * z) =
      ∑ d : R, φ d * ∑ h : R, ψ (h * (z - d)) := by
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun h _ => ?_
    rw [mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    ring
  rw [hswap]
  simp_rw [AddChar.sum_mulShift _ hψ, sub_eq_zero]
  simp [Finset.sum_ite_eq, mul_comm]

/-! ### The trace character in lattice coordinates -/

/-- The Eisenstein norm form. -/
def eisNormZ (a b : ℤ) : ℤ := a ^ 2 - a * b + b ^ 2

/-- The dual frequency of `n ↦ ψ_c(hn)` for `c = a + bω`, `h = p + qω`. -/
def thetaH (a b p q : ℤ) : E :=
  WithLp.toLp 2 ![((a * q - b * p : ℤ) : ℝ) / (eisNormZ a b : ℝ),
    ((a * p - a * q + b * q : ℤ) : ℝ) / (eisNormZ a b : ℝ)]

theorem inner_pt_thetaH (a b p q : ℤ) (n : Z) :
    inner ℝ (euclideanIntegerPoint n) (thetaH a b p q) =
      (((n 0) * (a * q - b * p) + (n 1) * (a * p - a * q + b * q) : ℤ) : ℝ) / (eisNormZ a b : ℝ) := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, thetaH, euclideanIntegerPoint, integerPoint,
    dotProduct, Fin.sum_univ_two, star_trivial, Matrix.cons_val_zero, Matrix.cons_val_one]
  push_cast
  ring

/-- **`ψ_c(hn)` is a lattice phase.** -/
theorem traceChar_mul_eval_eq_phase (a b p q : ℤ) (hc : eval a b ≠ 0) (n : Z) :
    principalTraceChar (eval a b) hc
        (Ideal.Quotient.mk (Ideal.span {eval a b}) (eval p q * eval (n 0) (n 1))) =
      phase (thetaH a b p q) (euclideanIntegerPoint n) := by
  rw [eval_mul, principalTraceChar_eval, phase, inner_pt_thetaH]
  congr 1
  unfold eisNormZ
  push_cast
  ring

/-! ### The dual frequencies are far from the lattice -/

/-- The norm form of a nonzero integer pair is at least one. -/
theorem one_le_eisNormZ {e₁ e₂ : ℤ} (h : e₁ ≠ 0 ∨ e₂ ≠ 0) : 1 ≤ eisNormZ e₁ e₂ := by
  unfold eisNormZ
  rcases h with h | h
  · nlinarith [sq_nonneg (e₁ - 2 * e₂), sq_nonneg e₂, sq_pos_of_ne_zero h,
      sq_nonneg (2 * e₁ - e₂)]
  · nlinarith [sq_nonneg (2 * e₁ - e₂), sq_pos_of_ne_zero h]

theorem eisNormZ_pos {a b : ℤ} (hc : eval a b ≠ 0) : 0 < eisNormZ a b := by
  have hne : a ≠ 0 ∨ b ≠ 0 := by
    by_contra h
    push Not at h
    apply hc
    rw [h.1, h.2]
    simp [eval]
  exact lt_of_lt_of_le one_pos (one_le_eisNormZ hne)

/-- **The integer core.** If `c = a + bω` does not divide `h = p + qω`, then for all integers
`m₀, m₁` the numerators `r = aq − bp − N m₀`, `s = ap − aq + bq − N m₁` satisfy
`3(r² + s²) ≥ 2N`. -/
theorem two_mul_eisNormZ_le (a b p q m₀ m₁ : ℤ) (hdiv : ¬ eval a b ∣ eval p q) :
    2 * eisNormZ a b ≤
      3 * ((a * q - b * p - eisNormZ a b * m₀) ^ 2 +
        (a * p - a * q + b * q - eisNormZ a b * m₁) ^ 2) := by
  -- `o = (m₀ + m₁) + m₀ ω` and `e = h − c·o`
  set s₀ := m₀ + m₁
  set t₀ := m₀
  set e₁ := p - (a * s₀ - b * t₀)
  set e₂ := q - (a * t₀ + b * s₀ - b * t₀)
  have he : e₁ ≠ 0 ∨ e₂ ≠ 0 := by
    by_contra h
    push Not at h
    apply hdiv
    refine ⟨eval s₀ t₀, ?_⟩
    rw [eval_mul]
    have h1 : p = a * s₀ - b * t₀ := by linarith [h.1]
    have h2 : q = a * t₀ + b * s₀ - b * t₀ := by linarith [h.2]
    rw [h1, h2]
  -- the coordinates `S, T` of `c̄ e`, and `(r, s) = (T, S − T)`
  set S := (a - b) * e₁ + b * e₂
  set T := a * e₂ - b * e₁
  have hr : a * q - b * p - eisNormZ a b * m₀ = T := by
    simp only [T, e₁, e₂, s₀, t₀, eisNormZ]; ring
  have hs : a * p - a * q + b * q - eisNormZ a b * m₁ = S - T := by
    simp only [S, T, e₁, e₂, s₀, t₀, eisNormZ]; ring
  have hnorm : S ^ 2 - S * T + T ^ 2 = eisNormZ a b * eisNormZ e₁ e₂ := by
    simp only [S, T, eisNormZ]; ring
  have he1 := one_le_eisNormZ he
  have hNpos : 0 ≤ eisNormZ a b := by
    unfold eisNormZ; nlinarith [sq_nonneg (a - b), sq_nonneg a, sq_nonneg b]
  rw [hr, hs]
  nlinarith [sq_nonneg (S - 2 * T), mul_le_mul_of_nonneg_left he1 hNpos]

/-- **The dual frequencies are far from the lattice.** If `c ∤ h`, then
`‖m − θ_h‖ ≥ √(2/(3N))` for every `m ∈ ℤ²`. -/
theorem sqrt_le_norm_sub_thetaH (a b p q : ℤ) (hc : eval a b ≠ 0)
    (hdiv : ¬ eval a b ∣ eval p q) (m : Z) :
    Real.sqrt (2 / (3 * (eisNormZ a b : ℝ))) ≤ ‖euclideanIntegerPoint m - thetaH a b p q‖ := by
  have hN : (0 : ℝ) < eisNormZ a b := by exact_mod_cast eisNormZ_pos hc
  have hcore := two_mul_eisNormZ_le a b p q (m 0) (m 1) hdiv
  have hcoreR : (2 : ℝ) * eisNormZ a b ≤
      3 * ((((a * q - b * p - eisNormZ a b * m 0 : ℤ)) : ℝ) ^ 2 +
        (((a * p - a * q + b * q - eisNormZ a b * m 1 : ℤ)) : ℝ) ^ 2) := by
    exact_mod_cast hcore
  -- the squared distance is `(r² + s²)/N²`
  have hdist : ‖euclideanIntegerPoint m - thetaH a b p q‖ ^ 2 =
      ((((a * q - b * p - eisNormZ a b * m 0 : ℤ)) : ℝ) ^ 2 +
        (((a * p - a * q + b * q - eisNormZ a b * m 1 : ℤ)) : ℝ) ^ 2) /
          (eisNormZ a b : ℝ) ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    simp only [Fin.sum_univ_two, thetaH, euclideanIntegerPoint, integerPoint,
      PiLp.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Real.norm_eq_abs, sq_abs]
    field_simp
    push_cast
    ring
  rw [Real.sqrt_le_left (by positivity)]
  rw [hdist, le_div_iff₀ (by positivity)]
  calc 2 / (3 * (eisNormZ a b : ℝ)) * (eisNormZ a b : ℝ) ^ 2 = 2 * eisNormZ a b / 3 := by
        field_simp
    _ ≤ _ := by linarith

/-! ### Reduction of a frequency to the unit cube -/

/-- The nearest lattice point. -/
def roundPoint (θ : E) : Z := fun i => round (θ i)

theorem phase_sub_pt (θ : E) (k n : Z) :
    phase (θ - euclideanIntegerPoint k) (euclideanIntegerPoint n) =
      phase θ (euclideanIntegerPoint n) := by
  unfold phase
  rw [inner_sub_right]
  have hint : inner ℝ (euclideanIntegerPoint n) (euclideanIntegerPoint k) =
      ((∑ i, n i * k i : ℤ) : ℝ) := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct, euclideanIntegerPoint, integerPoint,
      dotProduct, star_trivial]
    push_cast
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [hint]
  have h2 : ((2 * Real.pi * (inner ℝ (euclideanIntegerPoint n) θ -
      ((∑ i, n i * k i : ℤ) : ℝ)) : ℝ) : ℂ) * Complex.I =
      ((2 * Real.pi * inner ℝ (euclideanIntegerPoint n) θ : ℝ) : ℂ) * Complex.I -
        ((∑ i, n i * k i : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [h2, Complex.exp_sub, Complex.exp_int_mul_two_pi_mul_I, div_one]

theorem abs_sub_roundPoint_le (θ : E) (i : Fin 2) :
    |(θ - euclideanIntegerPoint (roundPoint θ)) i| ≤ 1 / 2 := by
  simp only [roundPoint, euclideanIntegerPoint, integerPoint, PiLp.sub_apply]
  exact abs_sub_round (θ i)

theorem norm_sub_reduce (θ : E) (m : Z) :
    ‖euclideanIntegerPoint m - (θ - euclideanIntegerPoint (roundPoint θ))‖ =
      ‖euclideanIntegerPoint (m + roundPoint θ) - θ‖ := by
  congr 1
  ext i
  simp only [euclideanIntegerPoint, integerPoint, PiLp.sub_apply, Pi.add_apply]
  push_cast
  ring

/-! ### Short columns of the Eisenstein lattice -/

/-- **Short columns of the Eisenstein lattice are incoherent.** Let `c = a + bω ≠ 0` and let `φ` be
a function on `O/(c)` of mean zero. For rows weighted by `f(Bn)`, `‖B^{−*}v‖ ≥ μ‖v‖`, and every
`M > 2`, the row sum `Σ_{n ∈ ℤ²} φ(n mod c) f(Bn)` is at most
`|det B|⁻¹ K (μ δ)^{−M} |O/(c)|⁻¹ Σ_h |φ̂(h)|` with `δ = √(2/(3N(c)))` and
`K = ‖f̂‖_{M,0} 9^M Σ_m ⟨m⟩^{−M}`. -/
theorem norm_tsum_eisensteinColumn_le (f : SchwartzMap E ℂ) {M : ℕ} (hM : (2 : ℝ) < M)
    (B : E ≃L[ℝ] E) {μ : ℝ} (hμ : 0 < μ) (hT : ∀ v, μ * ‖v‖ ≤ ‖inverseAdjoint B v‖)
    (a b : ℤ) [hc : NeZero (eval a b)] (φ : O ⧸ Ideal.span {eval a b} → ℂ)
    (hmean : ∑ d, φ d = 0) :
    ‖∑' n : Z, φ (Ideal.Quotient.mk _ (eval (n 0) (n 1))) * f (B (euclideanIntegerPoint n))‖ ≤
      latticeScale B * ((SchwartzMap.seminorm ℝ M 0 (𝓕 f) * (3 * 2 + 3) ^ M *
          ∑' m : Z, latticeBracket m ^ (-(M : ℝ))) *
          (μ * Real.sqrt (2 / (3 * (eisNormZ a b : ℝ)))) ^ (-(M : ℝ))) *
        ((Fintype.card (O ⧸ Ideal.span {eval a b}) : ℝ)⁻¹ *
          ∑ h : O ⧸ Ideal.span {eval a b},
            ‖∑ d, φ d * principalTraceChar (eval a b) hc.ne (-(h * d))‖) := by
  have hc0 : eval a b ≠ 0 := hc.ne
  set ψ := principalTraceChar (eval a b) hc0
  have hψ : ψ.IsPrimitive := principalTraceChar_primitive _ hc0
  have hcard : (0 : ℝ) < Fintype.card (O ⧸ Ideal.span {eval a b}) := by
    exact_mod_cast Fintype.card_pos
  have hN : (0 : ℝ) < eisNormZ a b := by exact_mod_cast eisNormZ_pos hc0
  set δ := Real.sqrt (2 / (3 * (eisNormZ a b : ℝ)))
  have hδ0 : 0 < δ := Real.sqrt_pos.mpr (by positivity)
  have hδ1 : δ ≤ 1 := by
    rw [Real.sqrt_le_one]
    have h1 : (1 : ℝ) ≤ eisNormZ a b := by exact_mod_cast (eisNormZ_pos hc0)
    rw [div_le_one (by positivity)]
    linarith
  -- dual coefficients
  set φh : O ⧸ Ideal.span {eval a b} → ℂ := fun h => ∑ d, φ d * ψ (-(h * d))
  have hφ0 : φh 0 = 0 := by
    simp only [φh, zero_mul, neg_zero, AddChar.map_zero_eq_one, mul_one]
    exact hmean
  -- representatives and their frequencies, reduced to the unit cube
  let rep : O ⧸ Ideal.span {eval a b} → O := fun h => Classical.choose (Ideal.Quotient.mk_surjective h)
  have hrep : ∀ h, Ideal.Quotient.mk _ (rep h) = h := fun h =>
    Classical.choose_spec (Ideal.Quotient.mk_surjective h)
  let pq : O ⧸ Ideal.span {eval a b} → ℤ × ℤ := fun h => coords (rep h)
  let θ0 : O ⧸ Ideal.span {eval a b} → E := fun h => thetaH a b (pq h).1 (pq h).2
  let θ : O ⧸ Ideal.span {eval a b} → E := fun h =>
    θ0 h - euclideanIntegerPoint (roundPoint (θ0 h))
  let s : Finset (O ⧸ Ideal.span {eval a b}) := Finset.univ.erase 0
  -- the column is a combination of lattice phases
  have hexp : ∀ n : Z, φ (Ideal.Quotient.mk _ (eval (n 0) (n 1))) =
      ∑ h ∈ s, (((Fintype.card (O ⧸ Ideal.span {eval a b}) : ℂ))⁻¹ * φh h) *
        phase (θ h) (euclideanIntegerPoint n) := by
    intro n
    have hinv := card_mul_eq_sum_dual hψ φ (Ideal.Quotient.mk _ (eval (n 0) (n 1)))
    have hcardC : ((Fintype.card (O ⧸ Ideal.span {eval a b}) : ℂ)) ≠ 0 := by
      exact_mod_cast hcard.ne'
    have hrw : ∀ h, ψ (h * Ideal.Quotient.mk _ (eval (n 0) (n 1))) =
        phase (θ h) (euclideanIntegerPoint n) := by
      intro h
      have hh : h = Ideal.Quotient.mk _ (eval (pq h).1 (pq h).2) := by
        simp only [pq, eval_coords, hrep]
      show _ = phase (θ0 h - euclideanIntegerPoint (roundPoint (θ0 h))) _
      rw [phase_sub_pt]
      conv_lhs => rw [hh, ← map_mul]
      exact traceChar_mul_eval_eq_phase a b _ _ hc0 n
    calc φ (Ideal.Quotient.mk _ (eval (n 0) (n 1))) =
          ((Fintype.card (O ⧸ Ideal.span {eval a b}) : ℂ))⁻¹ *
            (((Fintype.card (O ⧸ Ideal.span {eval a b}) : ℂ)) *
              φ (Ideal.Quotient.mk _ (eval (n 0) (n 1)))) := by field_simp
      _ = ((Fintype.card (O ⧸ Ideal.span {eval a b}) : ℂ))⁻¹ *
            ∑ h, φh h * ψ (h * Ideal.Quotient.mk _ (eval (n 0) (n 1))) := by rw [hinv]
      _ = ∑ h ∈ s, (((Fintype.card (O ⧸ Ideal.span {eval a b}) : ℂ))⁻¹ * φh h) *
            phase (θ h) (euclideanIntegerPoint n) := by
          rw [Finset.mul_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ 0), hφ0,
            zero_mul, mul_zero, zero_add]
          refine Finset.sum_congr rfl fun h _ => ?_
          rw [hrw]
          ring
  -- each nonzero class has a frequency at distance `≥ δ` from the lattice
  have hθ : ∀ h ∈ s, ∀ i, |θ h i| ≤ 1 / 2 := fun h _ i => abs_sub_roundPoint_le _ i
  have hfar : ∀ h ∈ s, ∀ m : Z, δ ≤ ‖euclideanIntegerPoint m - θ h‖ := by
    intro h hs m
    have hne : h ≠ 0 := Finset.ne_of_mem_erase hs
    have hdiv : ¬ eval a b ∣ eval (pq h).1 (pq h).2 := by
      intro hd
      apply hne
      have : eval (pq h).1 (pq h).2 = rep h := eval_coords _
      rw [this] at hd
      rw [← hrep h]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hd)
    show δ ≤ ‖euclideanIntegerPoint m - (θ0 h - euclideanIntegerPoint (roundPoint (θ0 h)))‖
    rw [norm_sub_reduce]
    exact sqrt_le_norm_sub_thetaH a b _ _ hc0 hdiv _
  have hmain := norm_tsum_column_le (d := 2) (by norm_num) f (by exact_mod_cast hM) B hμ hT s
    (fun h => ((Fintype.card (O ⧸ Ideal.span {eval a b}) : ℂ))⁻¹ * φh h) θ hθ hδ0 hδ1 hfar
  have hsum_eq : ∑' n : Z, φ (Ideal.Quotient.mk _ (eval (n 0) (n 1))) *
      f (B (euclideanIntegerPoint n)) =
      ∑' n : Z, (∑ h ∈ s, (((Fintype.card (O ⧸ Ideal.span {eval a b}) : ℂ))⁻¹ * φh h) *
        phase (θ h) (euclideanIntegerPoint n)) * f (B (euclideanIntegerPoint n)) := by
    congr 1
    funext n
    rw [hexp n]
  rw [hsum_eq]
  refine hmain.trans ?_
  have hK0 : 0 ≤ (SchwartzMap.seminorm ℝ M 0 (𝓕 f) * (3 * 2 + 3) ^ M *
          ∑' m : Z, latticeBracket m ^ (-(M : ℝ))) * (μ * δ) ^ (-(M : ℝ)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (apply_nonneg _ _) (by positivity))
      (tsum_nonneg fun _ => (Real.rpow_nonneg (latticeBracket_pos _).le _)))
      (Real.rpow_nonneg (mul_nonneg hμ.le hδ0.le) _)
  have hcast : ((2 : ℕ) : ℝ) = 2 := by norm_num
  simp only [hcast]
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (latticeScale_pos B).le hK0)
  calc ∑ h ∈ s, ‖((Fintype.card (O ⧸ Ideal.span {eval a b}) : ℂ))⁻¹ * φh h‖ =
        (Fintype.card (O ⧸ Ideal.span {eval a b}) : ℝ)⁻¹ * ∑ h ∈ s, ‖φh h‖ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun h _ => ?_
        rw [norm_mul, norm_inv, Complex.norm_natCast]
    _ ≤ (Fintype.card (O ⧸ Ideal.span {eval a b}) : ℝ)⁻¹ * ∑ h, ‖φh h‖ :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            fun _ _ _ => norm_nonneg _) (by positivity)

end GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies
