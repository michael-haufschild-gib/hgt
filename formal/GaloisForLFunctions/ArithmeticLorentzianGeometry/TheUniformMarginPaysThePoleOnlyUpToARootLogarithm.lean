import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheHodgeIndexHoldsAtAFixedFractionOfTheSpacing
import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheMetzlerThresholdOfTheOverlapRatioIsOne

/-!
# A uniform margin pays the pole only up to a root logarithm

The Hodge index of `ζ`'s atomic intersection form at a fixed fraction of the spacing
(`TheHodgeIndexHoldsAtAFixedFractionOfTheSpacing`) uses the *tilted* margin of the stability law,
which grows like `(m/8N) log m` along the atoms that carry the pole moment `∫ f e^{u/2}`. This file
shows that a uniform margin `M ⪰ μ‖·‖²` together with the pole row cannot reach a fixed overlap
ratio: the growth along the pole direction is necessary.

* **The rank-two bound** (`dot_sub_sqrt_mul_le_two_mul_dot`): for vectors `a, b, d`,
  `2(a·d)(b·d) ≥ (a·b − ‖a‖‖b‖)‖d‖²`, with equality at `d = ‖b‖a − ‖a‖b` (`two_mul_dot_witness`).
* **The margin model** (`marginModel_isHyperbolic_iff`): the Gram with pole plane, pole rows
  `a, b` and atom block `−m·1`, `m ≥ 0`, has one positive square iff `‖a‖‖b‖ − a·b ≤ m`. It is the
  extremal form with a uniform margin `m`.
* **The atomic pole rows** (`atomPoleRow_zero_apply`, `atomPoleRow_one_apply`): `a_n = n^{−1/2}α`,
  `b_n = n^{1/2}β` with the moments `α, β` of the bump, so `‖a‖‖b‖ − a·b = αβ(√(H_N S_N) − N)`,
  `H_N = Σ 1/n ≥ log(N + 1)`, `S_N = Σ n ≥ N²/2` (`sqrt_mul_sub_dot_atomPoleRow_ge`).
* **The barrier** (`not_isHyperbolic_marginModel_eventually`): for a dilated bump `g₁(·/(Kδ_N))` at
  a fixed overlap ratio `K > 0` and any fixed relative margin `μ`, the margin model is not
  hyperbolic for all large `N`: the gap grows like `K√(log N)`.

So a uniform margin pays the pole only up to `K√(log N) ≍ μ`. The pole row `(n^{−1/2}, n^{1/2})`
has `ℓ²`-size `√(log N) · N`, and only a margin that grows along `(n^{1/2})` — the tilt of the prime
rows — removes the logarithm.
-/

noncomputable section

open MeasureTheory Set Finset Matrix RHTower
open scoped Real

namespace GaloisForLFunctions.ArithmeticLorentzianGeometry

open GaloisForLFunctions.SpacingScaleHarmonicAnalysis GaloisForLFunctions.ArithmeticElectrostatics

/-! ### The rank-two bound -/

variable {κ : Type*} [Fintype κ]

theorem dot_self_nonneg' (a : κ → ℝ) : 0 ≤ a ⬝ᵥ a :=
  sum_nonneg fun i _ => mul_self_nonneg (a i)

theorem eq_zero_of_dot_self_eq_zero {a : κ → ℝ} (h : a ⬝ᵥ a = 0) : a = 0 := by
  funext i
  have := (sum_eq_zero_iff_of_nonneg fun j _ => mul_self_nonneg (a j)).mp h i (mem_univ i)
  simpa using this

/-- **The rank-two bound**: `2(a·d)(b·d) ≥ (a·b − ‖a‖‖b‖)‖d‖²`. -/
theorem dot_sub_sqrt_mul_le_two_mul_dot (a b d : κ → ℝ) :
    (a ⬝ᵥ b - Real.sqrt ((a ⬝ᵥ a) * (b ⬝ᵥ b))) * (d ⬝ᵥ d) ≤ 2 * (a ⬝ᵥ d) * (b ⬝ᵥ d) := by
  set p := Real.sqrt (a ⬝ᵥ a)
  set q := Real.sqrt (b ⬝ᵥ b)
  have hp2 : p ^ 2 = a ⬝ᵥ a := Real.sq_sqrt (dot_self_nonneg' a)
  have hq2 : q ^ 2 = b ⬝ᵥ b := Real.sq_sqrt (dot_self_nonneg' b)
  have hpq : Real.sqrt ((a ⬝ᵥ a) * (b ⬝ᵥ b)) = p * q := Real.sqrt_mul (dot_self_nonneg' a) _
  rw [hpq]
  have hD := dot_self_nonneg' d
  rcases (Real.sqrt_nonneg (a ⬝ᵥ a)).eq_or_lt with hp0 | hp0
  · have hp : p = 0 := hp0.symm
    have ha : a = 0 := eq_zero_of_dot_self_eq_zero (by rw [← hp2, hp]; ring)
    rw [hp, ha]; simp
  rcases (Real.sqrt_nonneg (b ⬝ᵥ b)).eq_or_lt with hq0 | hq0
  · have hq : q = 0 := hq0.symm
    have hb : b = 0 := eq_zero_of_dot_self_eq_zero (by rw [← hq2, hq]; ring)
    rw [hq, hb]; simp
  -- Cauchy–Schwarz for `q a − p b` against `d`
  set s := a ⬝ᵥ d
  set t := b ⬝ᵥ d
  have hCS := sum_mul_sq_le_sq_mul_sq univ (fun i => q * a i - p * b i) d
  have e1 : ∑ i, (q * a i - p * b i) * d i = q * s - p * t := by
    simp only [s, t, dotProduct, sub_mul, sum_sub_distrib, mul_assoc, ← mul_sum]
  have e2 : ∑ i, (q * a i - p * b i) ^ 2 = 2 * (p * q) * (p * q - a ⬝ᵥ b) := by
    have : ∑ i, (q * a i - p * b i) ^ 2 =
        q ^ 2 * (a ⬝ᵥ a) - 2 * (p * q) * (a ⬝ᵥ b) + p ^ 2 * (b ⬝ᵥ b) := by
      simp only [dotProduct, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
      exact sum_congr rfl fun i _ => by ring
    rw [this, ← hp2, ← hq2]; ring
  have e3 : ∑ i, d i ^ 2 = d ⬝ᵥ d := by simp only [dotProduct, sq]
  rw [e1, e2, e3] at hCS
  have hpq0 : 0 < p * q := mul_pos hp0 hq0
  have key : 0 ≤ p * q * (2 * s * t + (p * q - a ⬝ᵥ b) * (d ⬝ᵥ d)) := by
    nlinarith [sq_nonneg (q * s + p * t)]
  have := (mul_nonneg_iff_of_pos_left hpq0).mp key
  linarith

/-- **Equality in the rank-two bound** at `d = ‖b‖a − ‖a‖b`. -/
theorem two_mul_dot_witness (a b : κ → ℝ) :
    2 * (a ⬝ᵥ (Real.sqrt (b ⬝ᵥ b) • a - Real.sqrt (a ⬝ᵥ a) • b)) *
        (b ⬝ᵥ (Real.sqrt (b ⬝ᵥ b) • a - Real.sqrt (a ⬝ᵥ a) • b)) =
      -((Real.sqrt (a ⬝ᵥ a) * Real.sqrt (b ⬝ᵥ b) - a ⬝ᵥ b) *
        ((Real.sqrt (b ⬝ᵥ b) • a - Real.sqrt (a ⬝ᵥ a) • b) ⬝ᵥ
          (Real.sqrt (b ⬝ᵥ b) • a - Real.sqrt (a ⬝ᵥ a) • b))) ∧
    (Real.sqrt (b ⬝ᵥ b) • a - Real.sqrt (a ⬝ᵥ a) • b) ⬝ᵥ
        (Real.sqrt (b ⬝ᵥ b) • a - Real.sqrt (a ⬝ᵥ a) • b) =
      2 * (Real.sqrt (a ⬝ᵥ a) * Real.sqrt (b ⬝ᵥ b)) *
        (Real.sqrt (a ⬝ᵥ a) * Real.sqrt (b ⬝ᵥ b) - a ⬝ᵥ b) := by
  set p := Real.sqrt (a ⬝ᵥ a)
  set q := Real.sqrt (b ⬝ᵥ b)
  set d := q • a - p • b
  have hp2 : p ^ 2 = a ⬝ᵥ a := Real.sq_sqrt (dot_self_nonneg' a)
  have hq2 : q ^ 2 = b ⬝ᵥ b := Real.sq_sqrt (dot_self_nonneg' b)
  have hba : b ⬝ᵥ a = a ⬝ᵥ b := dotProduct_comm _ _
  have had : a ⬝ᵥ d = p * (p * q - a ⬝ᵥ b) := by
    simp only [d, dotProduct_sub, dotProduct_smul, smul_eq_mul, ← hp2]; ring
  have hbd : b ⬝ᵥ d = -(q * (p * q - a ⬝ᵥ b)) := by
    simp only [d, dotProduct_sub, dotProduct_smul, smul_eq_mul, ← hq2, hba]; ring
  have hdd : d ⬝ᵥ d = 2 * (p * q) * (p * q - a ⬝ᵥ b) := by
    have : d ⬝ᵥ d = q * (a ⬝ᵥ d) - p * (b ⬝ᵥ d) := by
      simp only [d, sub_dotProduct, smul_dotProduct, smul_eq_mul]
    rw [this, had, hbd]; ring
  refine ⟨?_, hdd⟩
  rw [had, hbd, hdd]; ring

/-! ### The margin model -/

variable [DecidableEq κ]

/-- The **margin model**: pole plane, pole rows `B`, atom block `−m·1`. -/
def marginModel (B : Matrix (Fin 2) κ ℝ) (m : ℝ) : Matrix (Fin 2 ⊕ κ) (Fin 2 ⊕ κ) ℝ :=
  fromBlocks realPolePlane B Bᵀ (-(m • (1 : Matrix κ κ ℝ)))

theorem polarDefect_marginModel (B : Matrix (Fin 2) κ ℝ) (m : ℝ) (d : κ → ℝ) :
    polarDefect B (-(m • (1 : Matrix κ κ ℝ))) d = 2 * (B 0 ⬝ᵥ d) * (B 1 ⬝ᵥ d) + m * (d ⬝ᵥ d) := by
  unfold polarDefect qf bil
  simp only [neg_mulVec, smul_mulVec, one_mulVec, dotProduct_neg, dotProduct_smul, smul_eq_mul]
  have h0 : (B *ᵥ d) 0 = B 0 ⬝ᵥ d := rfl
  have h1 : (B *ᵥ d) 1 = B 1 ⬝ᵥ d := rfl
  rw [h0, h1]; ring

/-- **The margin model is hyperbolic iff the margin pays the rank-two gap**:
`‖a‖‖b‖ − a·b ≤ m`, `a, b` the pole rows. -/
theorem marginModel_isHyperbolic_iff (B : Matrix (Fin 2) κ ℝ) {m : ℝ} (hm : 0 ≤ m) :
    IsHyperbolic (marginModel B m) ↔
      Real.sqrt ((B 0 ⬝ᵥ B 0) * (B 1 ⬝ᵥ B 1)) - B 0 ⬝ᵥ B 1 ≤ m := by
  have hL : (-(m • (1 : Matrix κ κ ℝ))).IsSymm := by
    unfold Matrix.IsSymm; rw [transpose_neg, transpose_smul, transpose_one]
  rw [marginModel, isHyperbolic_fromBlocks_iff _ hL]
  simp_rw [polarDefect_marginModel]
  set a := B 0
  set b := B 1
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    obtain ⟨hw1, hw2⟩ := two_mul_dot_witness a b
    set p := Real.sqrt (a ⬝ᵥ a)
    set q := Real.sqrt (b ⬝ᵥ b)
    have hpq : Real.sqrt ((a ⬝ᵥ a) * (b ⬝ᵥ b)) = p * q := Real.sqrt_mul (dot_self_nonneg' a) _
    rw [hpq] at hlt
    -- the gap is positive, so `p q > 0`
    have hpq0 : 0 < p * q := by
      by_contra h0
      push Not at h0
      have hpq' : p * q = 0 :=
        le_antisymm h0 (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      rcases mul_eq_zero.mp hpq' with hp | hq
      · have : a ⬝ᵥ a = 0 := by
          have h2 := Real.sq_sqrt (dot_self_nonneg' a)
          have hp' : Real.sqrt (a ⬝ᵥ a) = 0 := hp
          rw [← h2, hp']; norm_num
        rw [eq_zero_of_dot_self_eq_zero this, zero_dotProduct, hpq'] at hlt
        linarith
      · have : b ⬝ᵥ b = 0 := by
          have h2 := Real.sq_sqrt (dot_self_nonneg' b)
          have hq' : Real.sqrt (b ⬝ᵥ b) = 0 := hq
          rw [← h2, hq']; norm_num
        rw [eq_zero_of_dot_self_eq_zero this, dotProduct_zero, hpq'] at hlt
        linarith
    have hd := h (q • a - p • b)
    rw [hw1, hw2] at hd
    have : 0 < 2 * (p * q) * (p * q - a ⬝ᵥ b) := by
      have : 0 < p * q - a ⬝ᵥ b := by linarith
      positivity
    nlinarith
  · intro h d
    have := dot_sub_sqrt_mul_le_two_mul_dot a b d
    have hD := dot_self_nonneg' d
    nlinarith

/-! ### The atomic pole rows -/

variable {g : ℝ → ℝ} {w : ℝ}

/-- `∫ g_n e^{−u/2} = n^{−1/2} ∫ g e^{−v/2}`. -/
theorem atomPoleRow_zero_apply (g : ℝ → ℝ) {N : ℕ} (j : Fin N) :
    atomPoleRow g N 0 j =
      Real.exp (-(Real.log ((j : ℕ) + 1 : ℕ) / 2)) * ∫ v, g v * Real.exp (-(v / 2)) := by
  set c := Real.log ((j : ℕ) + 1 : ℕ)
  simp only [atomPoleRow, Matrix.of_apply, if_true, atom]
  rw [← integral_add_right_eq_self (fun u => g (u - c) * Real.exp (-(u / 2))) c,
    ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [add_sub_cancel_right]
  rw [show -((v + c) / 2) = -(c / 2) + -(v / 2) by ring, Real.exp_add]
  ring

/-- `∫ g_n e^{u/2} = n^{1/2} ∫ g e^{v/2}`. -/
theorem atomPoleRow_one_apply (g : ℝ → ℝ) {N : ℕ} (j : Fin N) :
    atomPoleRow g N 1 j = Real.exp (Real.log ((j : ℕ) + 1 : ℕ) / 2) * ∫ v, g v * Real.exp (v / 2) := by
  set c := Real.log ((j : ℕ) + 1 : ℕ)
  simp only [atomPoleRow, Matrix.of_apply, one_ne_zero, if_false, atom]
  rw [← integral_add_right_eq_self (fun u => g (u - c) * Real.exp (u / 2)) c,
    ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [add_sub_cancel_right]
  rw [show (v + c) / 2 = c / 2 + v / 2 by ring, Real.exp_add]
  ring

/-- The harmonic and Gauss sums of the atoms. -/
theorem atom_sums (N : ℕ) :
    Real.log (N + 1) ≤ ∑ j : Fin N, (1 : ℝ) / ((j : ℕ) + 1 : ℕ) ∧
      (N : ℝ) ^ 2 / 2 ≤ ∑ j : Fin N, (((j : ℕ) + 1 : ℕ) : ℝ) := by
  constructor
  · have h := log_add_one_le_harmonic N
    have e : (harmonic N : ℝ) = ∑ j : Fin N, (1 : ℝ) / ((j : ℕ) + 1 : ℕ) := by
      rw [_root_.harmonic_eq_sum_Icc]
      push_cast
      rw [sum_Icc_one_eq_sum_fin N (fun n => ((n : ℝ))⁻¹)]
      simp [one_div]
    rw [e] at h
    push_cast at h ⊢
    exact h
  · have key : ∀ M : ℕ, 2 * ∑ j ∈ Finset.range M, ((j : ℝ) + 1) = M * (M + 1) := fun M => by
      induction M with
      | zero => simp
      | succ M ih => rw [Finset.sum_range_succ, mul_add, ih]; push_cast; ring
    rw [Fin.sum_univ_eq_sum_range (fun j => (((j + 1 : ℕ)) : ℝ)) N]
    push_cast
    have h := key N
    nlinarith [sq_nonneg (N : ℝ), (N.cast_nonneg : (0 : ℝ) ≤ N)]

/-- **The rank-two gap of the atomic pole rows**: with `α = ∫ g e^{−v/2} ≥ 0`, `β = ∫ g e^{v/2} ≥ 0`,
`‖a‖‖b‖ − a·b ≥ αβ N (√(log(N + 1)/2) − 1)`. -/
theorem sqrt_mul_sub_dot_atomPoleRow_ge (g : ℝ → ℝ) {N : ℕ}
    (hα : 0 ≤ ∫ v, g v * Real.exp (-(v / 2))) (hβ : 0 ≤ ∫ v, g v * Real.exp (v / 2)) :
    (∫ v, g v * Real.exp (-(v / 2))) * (∫ v, g v * Real.exp (v / 2)) * N *
        (Real.sqrt (Real.log (N + 1) / 2) - 1) ≤
      Real.sqrt ((atomPoleRow g N 0 ⬝ᵥ atomPoleRow g N 0) *
        (atomPoleRow g N 1 ⬝ᵥ atomPoleRow g N 1)) - atomPoleRow g N 0 ⬝ᵥ atomPoleRow g N 1 := by
  set α := ∫ v, g v * Real.exp (-(v / 2))
  set β := ∫ v, g v * Real.exp (v / 2)
  set H := ∑ j : Fin N, (1 : ℝ) / ((j : ℕ) + 1 : ℕ)
  set S := ∑ j : Fin N, (((j : ℕ) + 1 : ℕ) : ℝ)
  have hpos : ∀ j : Fin N, (0 : ℝ) < (((j : ℕ) + 1 : ℕ) : ℝ) := fun j => by positivity
  have hsq : ∀ j : Fin N, Real.exp (Real.log ((j : ℕ) + 1 : ℕ) / 2) ^ 2 = (((j : ℕ) + 1 : ℕ) : ℝ) :=
    fun j => by rw [sq, ← Real.exp_add, add_halves, Real.exp_log (hpos j)]
  have hsq' : ∀ j : Fin N, Real.exp (-(Real.log ((j : ℕ) + 1 : ℕ) / 2)) ^ 2 =
      1 / (((j : ℕ) + 1 : ℕ) : ℝ) := fun j => by rw [Real.exp_neg, inv_pow, hsq j, one_div]
  have hsw : ∀ y z : ℝ, y * z * (y * z) = z ^ 2 * y ^ 2 := fun y z => by ring
  have haa : atomPoleRow g N 0 ⬝ᵥ atomPoleRow g N 0 = α ^ 2 * H := by
    simp only [dotProduct, atomPoleRow_zero_apply, H, mul_sum]
    exact sum_congr rfl fun j _ => by rw [hsw, hsq' j]
  have hbb : atomPoleRow g N 1 ⬝ᵥ atomPoleRow g N 1 = β ^ 2 * S := by
    simp only [dotProduct, atomPoleRow_one_apply, S, mul_sum]
    exact sum_congr rfl fun j _ => by rw [hsw, hsq j]
  have hab : atomPoleRow g N 0 ⬝ᵥ atomPoleRow g N 1 = α * β * N := by
    simp only [dotProduct, atomPoleRow_zero_apply, atomPoleRow_one_apply]
    have hterm : ∀ j : Fin N, Real.exp (-(Real.log ((j : ℕ) + 1 : ℕ) / 2)) * α *
        (Real.exp (Real.log ((j : ℕ) + 1 : ℕ) / 2) * β) = α * β := fun j => by
      rw [show ∀ x : ℝ, Real.exp (-x) * α * (Real.exp x * β) = (Real.exp (-x) * Real.exp x) * (α * β)
        from fun x => by ring, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
    rw [sum_congr rfl fun j _ => hterm j]
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  obtain ⟨hH, hS⟩ := atom_sums N
  have hL0 : 0 ≤ Real.log (N + 1) :=
    Real.log_nonneg (by linarith [(N.cast_nonneg : (0 : ℝ) ≤ N)])
  rw [haa, hbb, hab]
  -- `√(α²H β²S) = αβ√(HS) ≥ αβ N √(log(N+1)/2)`
  have hroot : α * β * N * Real.sqrt (Real.log (N + 1) / 2) ≤
      Real.sqrt (α ^ 2 * H * (β ^ 2 * S)) := by
    rw [show α ^ 2 * H * (β ^ 2 * S) = (α * β) ^ 2 * (H * S) by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (mul_nonneg hα hβ), mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hα hβ)
    rw [show (N : ℝ) * Real.sqrt (Real.log (N + 1) / 2) =
      Real.sqrt ((N : ℝ) ^ 2 * (Real.log (N + 1) / 2)) by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (N.cast_nonneg)]]
    refine Real.sqrt_le_sqrt ?_
    have : 0 ≤ (N : ℝ) ^ 2 / 2 := by positivity
    nlinarith
  have e : α * β * N * (Real.sqrt (Real.log (N + 1) / 2) - 1) =
      α * β * N * Real.sqrt (Real.log (N + 1) / 2) - α * β * N := by ring
  rw [e]
  linarith

/-! ### The barrier -/

variable {g₁ : ℝ → ℝ}

/-- **The margin barrier.** For a nonnegative nonzero `C²` profile `g₁` supported in `[0, 1]`, a
fixed overlap ratio `K > 0` and a fixed relative margin `μ ≥ 0`, the margin model of the atoms of
`g₁(·/(Kδ_N))` with atom block `−μ‖g‖²·1` is not hyperbolic for all large `N`. -/
theorem not_isHyperbolic_marginModel_eventually (hg₁ : ContDiff ℝ 2 g₁)
    (hg₁c : HasCompactSupport g₁) (hg₁0 : ∀ u, 0 ≤ g₁ u) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → g₁ u = 0)
    {u₀ : ℝ} (hu₀ : 0 < g₁ u₀) {K : ℝ} (hK : 0 < K) {μ : ℝ} (hμ : 0 ≤ μ) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ¬ IsHyperbolic (marginModel
      (atomPoleRow (dilate g₁ (K * atomSpacing N)) N)
      (μ * ∫ u, dilate g₁ (K * atomSpacing N) u ^ 2)) := by
  set A₁ := ∫ v, g₁ v
  set G₁ := ∫ v, g₁ v ^ 2
  have hA₁ : 0 < A₁ := Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (x := u₀) hg₁.continuous hg₁c hg₁0 hu₀.ne'
  have hG₁ : 0 ≤ G₁ := integral_nonneg fun _ => sq_nonneg _
  set T := 2 * Real.exp (1 / 2) * μ * G₁ / (K * A₁ ^ 2)
  have hT : 0 ≤ T := by positivity
  refine ⟨⌈K⌉₊ + ⌈Real.exp (2 * (1 + T) ^ 2)⌉₊ + 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hNK : K ≤ N := by
    have := Nat.le_ceil K; have : (⌈K⌉₊ : ℝ) ≤ N := by exact_mod_cast (by omega : ⌈K⌉₊ ≤ N)
    linarith
  have hNexp : Real.exp (2 * (1 + T) ^ 2) < N + 1 := by
    have h1 := Nat.le_ceil (Real.exp (2 * (1 + T) ^ 2))
    have h2 : (⌈Real.exp (2 * (1 + T) ^ 2)⌉₊ : ℝ) + 1 ≤ N + 1 := by
      exact_mod_cast (by omega : ⌈Real.exp (2 * (1 + T) ^ 2)⌉₊ + 1 ≤ N + 1)
    linarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  set δ := atomSpacing N
  set w := K * δ
  have hδ := atomSpacing_pos hN1
  have hw0 : 0 < w := by positivity
  have hδhi : δ ≤ 1 / N := atomSpacing_le_inv hN1
  have hδlo : 1 / ((N : ℝ) + 1) ≤ δ := inv_succ_le_atomSpacing hN1
  have hw1 : w ≤ 1 := by
    calc w = K * δ := rfl
      _ ≤ K * (1 / N) := mul_le_mul_of_nonneg_left hδhi hK.le
      _ ≤ 1 := by rw [mul_one_div, div_le_one hNpos]; exact hNK
  -- the bump moments
  set g := dilate g₁ w
  have hg := (contDiff_dilate hg₁ w).continuous
  have hgs := dilate_supp hsupp hw0
  have hg0 : ∀ u, 0 ≤ g u := fun u => hg₁0 _
  have hgc := hasCompactSupport_dilate hsupp hw0
  have hint : ∀ φ : ℝ → ℝ, Continuous φ → Integrable fun v => g v * φ v := fun φ hφ =>
    (hg.mul hφ).integrable_of_hasCompactSupport hgc.mul_right
  have hgi : Integrable g := hg.integrable_of_hasCompactSupport hgc
  have hα : Real.exp (-(w / 2)) * (w * A₁) ≤ ∫ v, g v * Real.exp (-(v / 2)) := by
    rw [← integral_dilate hw0, ← integral_const_mul]
    refine integral_mono (hgi.const_mul _) (hint _ (by fun_prop)) fun v => ?_
    by_cases hv : v ∈ Set.Icc 0 w
    · rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [hv.2])) (hg0 v)
    · simp [g, hgs v hv]
  have hβ : w * A₁ ≤ ∫ v, g v * Real.exp (v / 2) := by
    rw [← integral_dilate hw0]
    refine integral_mono hgi (hint _ (by fun_prop)) fun v => ?_
    by_cases hv : v ∈ Set.Icc 0 w
    · exact le_mul_of_one_le_right (hg0 v) (Real.one_le_exp (by linarith [hv.1]))
    · simp [g, hgs v hv]
  have hα0 : 0 ≤ ∫ v, g v * Real.exp (-(v / 2)) := le_trans (by positivity) hα
  have hβ0 : 0 ≤ ∫ v, g v * Real.exp (v / 2) := le_trans (by positivity) hβ
  have hgap := sqrt_mul_sub_dot_atomPoleRow_ge g (N := N) hα0 hβ0
  -- the root logarithm beats the margin
  have hroot : 1 + T < Real.sqrt (Real.log (N + 1) / 2) := by
    rw [Real.lt_sqrt (by positivity)]
    have : 2 * (1 + T) ^ 2 < Real.log (N + 1) := by
      rw [Real.lt_log_iff_exp_lt (by positivity)]; exact hNexp
    linarith
  have hwN : K / 2 ≤ w * N := by
    have h1 : K * (1 / ((N : ℝ) + 1)) * N ≤ w * N :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hδlo hK.le) hNpos.le
    have h2 : K * (1 / ((N : ℝ) + 1)) * N = K * (N / ((N : ℝ) + 1)) := by ring
    have h3 : (1 : ℝ) / 2 ≤ N / ((N : ℝ) + 1) := by
      have : (1 : ℝ) ≤ N := by exact_mod_cast hN1
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]; linarith
    nlinarith
  rw [marginModel_isHyperbolic_iff _ (by rw [integral_dilate_sq hw0]; positivity),
    integral_dilate_sq hw0]
  intro hle
  have he : Real.exp (-(1 / 2)) ≤ Real.exp (-(w / 2)) := Real.exp_le_exp.mpr (by linarith)
  have heh : Real.exp (-(1 / 2)) * Real.exp (1 / 2) = 1 := by rw [← Real.exp_add]; simp
  set α := ∫ v, g v * Real.exp (-(v / 2))
  set β := ∫ v, g v * Real.exp (v / 2)
  have h1 : Real.exp (-(1 / 2)) * (w * A₁) ≤ α :=
    le_trans (mul_le_mul_of_nonneg_right he (by positivity)) hα
  have hlow : Real.exp (-(1 / 2)) * (w * A₁) * (w * A₁) * N ≤ α * β * N :=
    mul_le_mul_of_nonneg_right (mul_le_mul h1 hβ (by positivity) hα0) hNpos.le
  have hαβN : 0 < α * β * N := lt_of_lt_of_le (by positivity) hlow
  -- `αβN(√(…) − 1) > αβN T ≥ e^{−1/2}(wA₁)²N T = (2wN/K) μ w G₁ ≥ μ w G₁`
  have hstrict : α * β * N * T < α * β * N * (Real.sqrt (Real.log (N + 1) / 2) - 1) :=
    mul_lt_mul_of_pos_left (by linarith) hαβN
  have hmid : Real.exp (-(1 / 2)) * (w * A₁) * (w * A₁) * N * T ≤ α * β * N * T :=
    mul_le_mul_of_nonneg_right hlow hT
  have hKne : K ≠ 0 := hK.ne'
  have hAne : A₁ ≠ 0 := hA₁.ne'
  have hval : Real.exp (-(1 / 2)) * (w * A₁) * (w * A₁) * N * T =
      (Real.exp (-(1 / 2)) * Real.exp (1 / 2)) * (2 * (w * N) / K * (μ * (w * G₁))) := by
    simp only [T]; field_simp
  rw [heh, one_mul] at hval
  have hge : μ * (w * G₁) ≤ 2 * (w * N) / K * (μ * (w * G₁)) := by
    have : 1 ≤ 2 * (w * N) / K := by rw [le_div_iff₀ hK]; linarith
    exact le_mul_of_one_le_left (by positivity) this
  linarith

end GaloisForLFunctions.ArithmeticLorentzianGeometry
