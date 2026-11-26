import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.TenthPlateau.NonAbelianClawOnset

/-! # Hidden locally rotated Ising survival tubes inside `Ω_claw(η)`

This module constructs the Pythagorean `SU(2)^⊗N` local gauge transformation (`pythRotMat ∈ SO(3)`
with entries in `(1 / 3) ℤ` and `pythUnitary ∈ U(2)`) and proves that basis-wise Pauli-claw
conditioning `Ω_claw(k + 1, η)` — and even `allCoordStrongEvent (k + 1) η` — admits `(N - 1)`-gate
all-time survival tubes (`gaussian_hiddenRotatedIsing_claw_tube_tail`) with `pathPauliDisorderLaw`
probability `≥ c(k, η) * T ^ -(10 * k + 22)` and `T < tenthPlateauOnset H s` for all
`k + 2 ≤ s ≤ nearHilbertContinuousCircuitBudget (k + 3)`. -/

open Set Filter MeasureTheory ProbabilityTheory Real Topology Matrix NormedSpace
open scoped Matrix.Norms.L2Operator ENNReal NNReal ComplexConjugate
namespace GaloisForLFunctions.HTGeometry.AccuracyScales.TenthPlateau
open SharpOccupation SharpOccupation.FiniteRecords MaximumIntervals
open WeakBonds PrescribedTimes SpanningDensity.FixedHorizon
open OrdinaryTwoLocalGaussianHarmonicChoiGrowthLaw GaloisForLFunctions.RHTower
noncomputable section

private abbrev Config (N : ℕ) := Fin N → Bool
private abbrev Realizes {n : ℕ} := @DiagonalSynthesis.Realizes n

/-- Rational Pythagorean orthogonal matrix `O_pyth ∈ SO(3)` with strictly nonzero third column
`(2/3, 2/3, 1/3)ᵀ`. -/
def pythRotMat : Matrix (Fin 3) (Fin 3) ℝ := fun i j =>
  match i, j with
  | 0, 0 => 2 / 3 | 0, 1 => -1 / 3 | 0, 2 => 2 / 3
  | 1, 0 => -1 / 3 | 1, 1 => 2 / 3 | 1, 2 => 2 / 3
  | 2, 0 => -2 / 3 | 2, 1 => -2 / 3 | 2, 2 => 1 / 3

private theorem pythRotMat_orthog :
    pythRotMatᵀ * pythRotMat = 1 ∧ pythRotMat * pythRotMatᵀ = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pythRotMat, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num

/-- Unnormalized Gaussian-integer `2 × 2` core of `pythUnitary`. -/
private def pythIntMat : Matrix Bool Bool ℂ := fun x y =>
  match x, y with
  | false, false => 2
  | false, true => -1 + Complex.I
  | true, false => 1 + Complex.I
  | true, true => 2

/-- Single-qubit Pythagorean unitary `R_pyth ∈ U(2)` inducing `pythRotMat` on `(X, Y, Z)`. -/
def pythUnitary : Matrix Bool Bool ℂ :=
  ((1 / Real.sqrt 6 : ℝ) : ℂ) • pythIntMat

private theorem pythUnitary_mem_unitary :
    star pythUnitary * pythUnitary = 1 ∧ pythUnitary * star pythUnitary = 1 := by
  have hsq : (((1 / Real.sqrt 6 : ℝ) : ℂ) * ((1 / Real.sqrt 6 : ℝ) : ℂ)) = (1 / 6 : ℂ) := by
    have h1 : (1 / Real.sqrt 6 : ℝ) * (1 / Real.sqrt 6 : ℝ) = 1 / 6 := by
      rw [div_mul_div_comm, one_mul, ← sq, Real.sq_sqrt (by norm_num)]
    rw [← Complex.ofReal_mul, h1]; norm_num
  have hst : star pythUnitary = ((1 / Real.sqrt 6 : ℝ) : ℂ) • star pythIntMat := by
    rw [pythUnitary, star_smul, Complex.star_def, Complex.conj_ofReal]
  have hint1 : star pythIntMat * pythIntMat = (6 : ℂ) • 1 := by
    ext x y; fin_cases x <;> fin_cases y <;>
      simp [pythIntMat, Matrix.mul_apply, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_apply, Matrix.smul_apply, map_ofNat] <;>
      norm_num [Complex.ext_iff]
  have hint2 : pythIntMat * star pythIntMat = (6 : ℂ) • 1 := by
    ext x y; fin_cases x <;> fin_cases y <;>
      simp [pythIntMat, Matrix.mul_apply, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_apply, Matrix.smul_apply, map_ofNat] <;>
      norm_num [Complex.ext_iff]
  refine ⟨?_, ?_⟩
  · rw [hst, pythUnitary, smul_mul_smul_comm, hsq, hint1, smul_smul]; norm_num
  · rw [hst, pythUnitary, smul_mul_smul_comm, hsq, hint2, smul_smul]; norm_num

private theorem pythUnitary_conj_pauli (b : Fin 3) :
    pythUnitary * finiteQubitPauli b * star pythUnitary =
      ∑ a : Fin 3, ((pythRotMat a b : ℝ) : ℂ) • finiteQubitPauli a := by
  have hsq : (((1 / Real.sqrt 6 : ℝ) : ℂ) * ((1 / Real.sqrt 6 : ℝ) : ℂ)) = (1 / 6 : ℂ) := by
    have h1 : (1 / Real.sqrt 6 : ℝ) * (1 / Real.sqrt 6 : ℝ) = 1 / 6 := by
      rw [div_mul_div_comm, one_mul, ← sq, Real.sq_sqrt (by norm_num)]
    rw [← Complex.ofReal_mul, h1]; norm_num
  have hst : star pythUnitary = ((1 / Real.sqrt 6 : ℝ) : ℂ) • star pythIntMat := by
    rw [pythUnitary, star_smul, Complex.star_def, Complex.conj_ofReal]
  have hmul : pythUnitary * finiteQubitPauli b * star pythUnitary =
      (1 / 6 : ℂ) • (pythIntMat * finiteQubitPauli b * star pythIntMat) := by
    rw [hst, pythUnitary, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, hsq]
  rw [hmul]
  fin_cases b <;> ext x y <;> fin_cases x <;> fin_cases y <;>
    simp [pythIntMat, pythRotMat, finiteQubitPauli, Matrix.mul_apply,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
      Fin.sum_univ_three, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, map_ofNat] <;>
    norm_num [Complex.ext_iff]

/-- Sitewise tensor-product matrix `⨂_{s : Fin N} R_s` on `Register N`. -/
def prodLocalMatrix {N : ℕ} (R : Fin N → Matrix Bool Bool ℂ) : Register N :=
  fun x y => ∏ s : Fin N, R s (x s) (y s)

theorem prodLocalMatrix_mul {N : ℕ} (R S : Fin N → Matrix Bool Bool ℂ) :
    prodLocalMatrix R * prodLocalMatrix S = prodLocalMatrix (fun s => R s * S s) := by
  ext x z
  simp only [prodLocalMatrix, Matrix.mul_apply, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum fun s b => R s (x s) b * S s b (z s)).symm

theorem prodLocalMatrix_star {N : ℕ} (R : Fin N → Matrix Bool Bool ℂ) :
    star (prodLocalMatrix R) = prodLocalMatrix (fun s => star (R s)) := by
  ext x y
  simp only [prodLocalMatrix, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    Complex.star_def, map_prod]

theorem prodLocalMatrix_one {N : ℕ} :
    prodLocalMatrix (fun _ : Fin N => (1 : Matrix Bool Bool ℂ)) = 1 := by
  ext x y
  simp only [prodLocalMatrix]
  by_cases hxy : x = y
  · subst hxy; simp
  · rw [Matrix.one_apply_ne hxy]
    obtain ⟨s, hs⟩ := Function.ne_iff.mp hxy
    exact Finset.prod_eq_zero (Finset.mem_univ s) (Matrix.one_apply_ne hs)

theorem prodLocalMatrix_mem_unitary {N : ℕ} (R : Fin N → Matrix Bool Bool ℂ)
    (hR : ∀ s, star (R s) * R s = 1 ∧ R s * star (R s) = 1) :
    prodLocalMatrix R ∈ unitary (Register N) := by
  rw [Unitary.mem_iff, prodLocalMatrix_star, prodLocalMatrix_mul, prodLocalMatrix_mul]
  refine ⟨?_, ?_⟩
  · rw [show (fun s => star (R s) * R s) = fun _ => 1 from funext fun s => (hR s).1]
    exact prodLocalMatrix_one
  · rw [show (fun s => R s * star (R s)) = fun _ => 1 from funext fun s => (hR s).2]
    exact prodLocalMatrix_one

theorem prodLocalMatrix_conj_pauli {N : ℕ} (R : Fin N → Matrix Bool Bool ℂ)
    (P : Fin N → Option (Fin 3)) :
    prodLocalMatrix R * finitePauliMatrix P * star (prodLocalMatrix R) =
      prodLocalMatrix (fun s => R s * boolPauliOption (P s) * star (R s)) := by
  have hP : finitePauliMatrix P = prodLocalMatrix (fun s => boolPauliOption (P s)) := rfl
  rw [hP, prodLocalMatrix_star, prodLocalMatrix_mul, prodLocalMatrix_mul]

private theorem sum4_comm {α β γ δ M : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [AddCommMonoid M] (f : α → β → γ → δ → M) :
    (∑ a : α, ∑ b : β, ∑ c : γ, ∑ d : δ, f a b c d) =
      ∑ c : γ, ∑ d : δ, ∑ a : α, ∑ b : β, f a b c d := by
  calc ∑ a : α, ∑ b : β, ∑ c : γ, ∑ d : δ, f a b c d
      = ∑ a : α, ∑ c : γ, ∑ b : β, ∑ d : δ, f a b c d :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ c : γ, ∑ a : α, ∑ b : β, ∑ d : δ, f a b c d :=
          Finset.sum_comm
    _ = ∑ c : γ, ∑ a : α, ∑ d : δ, ∑ b : β, f a b c d :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ c : γ, ∑ d : δ, ∑ a : α, ∑ b : β, f a b c d :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm

/-- Block-diagonal orthogonal action of `W_pyth = R_pyth^{⊗(n + 2)}` on `PathLabel n → ℝ`. -/
def pythShellMap (n : ℕ) (u : PathLabel n → ℝ) : PathLabel n → ℝ
  | .inl (v, a) => ∑ b : Fin 3, pythRotMat a b * u (.inl (v, b))
  | .inr (e, (a₁, a₂)) =>
      ∑ b₁ : Fin 3, ∑ b₂ : Fin 3, pythRotMat a₁ b₁ * pythRotMat a₂ b₂ * u (.inr (e, (b₁, b₂)))

/-- Inverse block-diagonal orthogonal action (`pythRotMatᵀ`) on `PathLabel n → ℝ`. -/
def pythShellInv (n : ℕ) (u : PathLabel n → ℝ) : PathLabel n → ℝ
  | .inl (v, b) => ∑ a : Fin 3, pythRotMat a b * u (.inl (v, a))
  | .inr (e, (b₁, b₂)) =>
      ∑ a₁ : Fin 3, ∑ a₂ : Fin 3, pythRotMat a₁ b₁ * pythRotMat a₂ b₂ * u (.inr (e, (a₁, a₂)))

private theorem pythShellInv_left (n : ℕ) (z : PathLabel n → ℝ) :
    pythShellInv n (pythShellMap n z) = z := by
  obtain ⟨hL, _⟩ := pythRotMat_orthog
  have hcol (b₁ b₂ : Fin 3) : (∑ a : Fin 3, pythRotMat a b₁ * pythRotMat a b₂) =
      if b₁ = b₂ then 1 else 0 := by
    have h := congrFun (congrFun hL b₁) b₂
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using h
  funext l
  rcases l with ⟨v, b⟩ | ⟨e, ⟨b₁, b₂⟩⟩
  · simp only [pythShellInv, pythShellMap, Finset.mul_sum]
    rw [Finset.sum_comm]
    have hs : (∑ c : Fin 3, ∑ a : Fin 3, pythRotMat a b * (pythRotMat a c * z (.inl (v, c)))) =
        ∑ c : Fin 3, (∑ a : Fin 3, pythRotMat a b * pythRotMat a c) * z (.inl (v, c)) :=
      Finset.sum_congr rfl fun c _ => by rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => by ring
    rw [hs]; simp_rw [hcol b]; simp
  · simp only [pythShellInv, pythShellMap]
    have hfact : (∑ a₁ : Fin 3, ∑ a₂ : Fin 3,
        pythRotMat a₁ b₁ * pythRotMat a₂ b₂ *
          ∑ c₁ : Fin 3, ∑ c₂ : Fin 3, pythRotMat a₁ c₁ * pythRotMat a₂ c₂ * z (.inr (e, (c₁, c₂)))) =
        ∑ c₁ : Fin 3, ∑ c₂ : Fin 3,
          (∑ a₁ : Fin 3, pythRotMat a₁ b₁ * pythRotMat a₁ c₁) *
            (∑ a₂ : Fin 3, pythRotMat a₂ b₂ * pythRotMat a₂ c₂) * z (.inr (e, (c₁, c₂))) := by
      calc _ = ∑ a₁ : Fin 3, ∑ a₂ : Fin 3, ∑ c₁ : Fin 3, ∑ c₂ : Fin 3,
              pythRotMat a₁ b₁ * pythRotMat a₂ b₂ *
                (pythRotMat a₁ c₁ * pythRotMat a₂ c₂ * z (.inr (e, (c₁, c₂)))) := by
                refine Finset.sum_congr rfl fun a₁ _ => Finset.sum_congr rfl fun a₂ _ => ?_
                rw [Finset.mul_sum]
                exact Finset.sum_congr rfl fun c₁ _ => Finset.mul_sum ..
        _ = ∑ c₁ : Fin 3, ∑ c₂ : Fin 3, ∑ a₁ : Fin 3, ∑ a₂ : Fin 3,
              pythRotMat a₁ b₁ * pythRotMat a₂ b₂ *
                (pythRotMat a₁ c₁ * pythRotMat a₂ c₂ * z (.inr (e, (c₁, c₂)))) := sum4_comm _
        _ = _ := by
              refine Finset.sum_congr rfl fun c₁ _ => Finset.sum_congr rfl fun c₂ _ => ?_
              rw [Finset.sum_mul, Finset.sum_mul]
              refine Finset.sum_congr rfl fun a₁ _ => ?_
              rw [Finset.mul_sum, Finset.sum_mul]
              exact Finset.sum_congr rfl fun a₂ _ => by ring
    rw [hfact]; simp_rw [hcol b₁, hcol b₂]; simp

private theorem pythShellInv_right (n : ℕ) (x_lbl : PathLabel n → ℝ) :
    pythShellMap n (pythShellInv n x_lbl) = x_lbl := by
  obtain ⟨_, hR⟩ := pythRotMat_orthog
  have hrow (a₁ a₂ : Fin 3) : (∑ b : Fin 3, pythRotMat a₁ b * pythRotMat a₂ b) =
      if a₁ = a₂ then 1 else 0 := by
    have h := congrFun (congrFun hR a₁) a₂
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using h
  funext l
  rcases l with ⟨v, a⟩ | ⟨e, ⟨a₁, a₂⟩⟩
  · simp only [pythShellMap, pythShellInv, Finset.mul_sum]
    rw [Finset.sum_comm]
    have hs : (∑ d : Fin 3, ∑ b : Fin 3, pythRotMat a b * (pythRotMat d b * x_lbl (.inl (v, d)))) =
        ∑ d : Fin 3, (∑ b : Fin 3, pythRotMat a b * pythRotMat d b) * x_lbl (.inl (v, d)) :=
      Finset.sum_congr rfl fun d _ => by rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => by ring
    rw [hs]; simp_rw [hrow a]; simp
  · simp only [pythShellMap, pythShellInv]
    have hfact : (∑ b₁ : Fin 3, ∑ b₂ : Fin 3,
        pythRotMat a₁ b₁ * pythRotMat a₂ b₂ *
          ∑ d₁ : Fin 3, ∑ d₂ : Fin 3, pythRotMat d₁ b₁ * pythRotMat d₂ b₂ * x_lbl (.inr (e, (d₁, d₂)))) =
        ∑ d₁ : Fin 3, ∑ d₂ : Fin 3,
          (∑ b₁ : Fin 3, pythRotMat a₁ b₁ * pythRotMat d₁ b₁) *
            (∑ b₂ : Fin 3, pythRotMat a₂ b₂ * pythRotMat d₂ b₂) * x_lbl (.inr (e, (d₁, d₂))) := by
      calc _ = ∑ b₁ : Fin 3, ∑ b₂ : Fin 3, ∑ d₁ : Fin 3, ∑ d₂ : Fin 3,
              pythRotMat a₁ b₁ * pythRotMat a₂ b₂ *
                (pythRotMat d₁ b₁ * pythRotMat d₂ b₂ * x_lbl (.inr (e, (d₁, d₂)))) := by
                refine Finset.sum_congr rfl fun b₁ _ => Finset.sum_congr rfl fun b₂ _ => ?_
                rw [Finset.mul_sum]
                exact Finset.sum_congr rfl fun d₁ _ => Finset.mul_sum ..
        _ = ∑ d₁ : Fin 3, ∑ d₂ : Fin 3, ∑ b₁ : Fin 3, ∑ b₂ : Fin 3,
              pythRotMat a₁ b₁ * pythRotMat a₂ b₂ *
                (pythRotMat d₁ b₁ * pythRotMat d₂ b₂ * x_lbl (.inr (e, (d₁, d₂)))) := sum4_comm _
        _ = _ := by
              refine Finset.sum_congr rfl fun d₁ _ => Finset.sum_congr rfl fun d₂ _ => ?_
              rw [Finset.sum_mul, Finset.sum_mul]
              refine Finset.sum_congr rfl fun b₁ _ => ?_
              rw [Finset.mul_sum, Finset.sum_mul]
              exact Finset.sum_congr rfl fun b₂ _ => by ring
    rw [hfact]; simp_rw [hrow a₁, hrow a₂]; simp

private theorem pythShellMap_measurePreserving (n : ℕ) :
    MeasurePreserving (pythShellMap n)
      (Measure.pi fun _ : PathLabel n => gaussianReal 0 1)
      (Measure.pi fun _ : PathLabel n => gaussianReal 0 1) := by
  let O_blk : Matrix (PathLabel n) (PathLabel n) ℝ := fun l₁ l₂ =>
    match l₁, l₂ with
    | .inl (v₁, a), .inl (v₂, b) => if v₁ = v₂ then pythRotMat a b else 0
    | .inr (e₁, (a₁, a₂)), .inr (e₂, (b₁, b₂)) =>
        if e₁ = e₂ then pythRotMat a₁ b₁ * pythRotMat a₂ b₂ else 0
    | _, _ => 0
  have hmul_eq (u : PathLabel n → ℝ) : pythShellMap n u = O_blk *ᵥ u := by
    funext l
    rcases l with ⟨v, a⟩ | ⟨e, ⟨a₁, a₂⟩⟩
    · simp only [pythShellMap, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
      rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
      have hr : (∑ x : Fin (n + 1), ∑ y : Fin 3 × Fin 3, O_blk (.inl (v, a)) (.inr (x, y)) * u (.inr (x, y))) = 0 := by
        simp [O_blk]
      rw [hr, add_zero, Finset.sum_eq_single v]
      · simp [O_blk]
      · intro v' _ hne; simp [O_blk, hne.symm]
      · simp
    · simp only [pythShellMap, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
      rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
      have hl : (∑ x : Fin (n + 2), ∑ y : Fin 3, O_blk (.inr (e, (a₁, a₂))) (.inl (x, y)) * u (.inl (x, y))) = 0 := by
        simp [O_blk]
      rw [hl, zero_add, Finset.sum_eq_single e]
      · simp [O_blk, Fintype.sum_prod_type]
      · intro e' _ hne; simp [O_blk, hne.symm]
      · simp
  have hO_left : O_blkᵀ * O_blk = 1 := by
    obtain ⟨hL, _⟩ := pythRotMat_orthog
    have hcol (b₁ b₂ : Fin 3) : (∑ a : Fin 3, pythRotMat a b₁ * pythRotMat a b₂) =
        if b₁ = b₂ then 1 else 0 := by
      have h := congrFun (congrFun hL b₁) b₂
      simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using h
    ext l₁ l₂
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_sum_type,
      Fintype.sum_prod_type, Matrix.one_apply]
    rcases l₁ with ⟨v₁, b₁⟩ | ⟨e₁, ⟨b₁, b₂⟩⟩ <;> rcases l₂ with ⟨v₂, c₁⟩ | ⟨e₂, ⟨c₁, c₂⟩⟩
    · simp only [O_blk, mul_zero, Finset.sum_const_zero, add_zero]
      by_cases hv : v₁ = v₂
      · subst hv
        rw [Finset.sum_eq_single v₁]
        · simp [hcol b₁ c₁, Prod.ext_iff]
        · intro v _ hne; simp [hne]
        · simp
      · rw [if_neg (by simp [hv])]
        refine Finset.sum_eq_zero fun v _ => Finset.sum_eq_zero fun a _ => ?_
        by_cases h1 : v = v₁
        · subst h1; simp [hv]
        · simp [h1]
    · simp [O_blk]
    · simp [O_blk]
    · simp only [O_blk, mul_zero, Finset.sum_const_zero, zero_add]
      by_cases he : e₁ = e₂
      · subst he
        rw [Finset.sum_eq_single e₁]
        · simp only [↓reduceIte]
          have hfact : (∑ a₁ : Fin 3, ∑ a₂ : Fin 3,
              (pythRotMat a₁ b₁ * pythRotMat a₂ b₂) * (pythRotMat a₁ c₁ * pythRotMat a₂ c₂)) =
              (∑ a₁ : Fin 3, pythRotMat a₁ b₁ * pythRotMat a₁ c₁) *
                (∑ a₂ : Fin 3, pythRotMat a₂ b₂ * pythRotMat a₂ c₂) := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun a₁ _ => ?_
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun a₂ _ => by ring
          rw [hfact, hcol b₁ c₁, hcol b₂ c₂]
          by_cases h1 : b₁ = c₁ <;> by_cases h2 : b₂ = c₂ <;> simp [h1, h2]
        · intro e _ hne; simp [hne]
        · simp
      · rw [if_neg (by simp [he])]
        refine Finset.sum_eq_zero fun e _ => Finset.sum_eq_zero fun pq _ => ?_
        by_cases h1 : e = e₁
        · subst h1; simp [he]
        · simp [h1]
  have hO_right : O_blk * O_blkᵀ = 1 := by
    obtain ⟨_, hR⟩ := pythRotMat_orthog
    have hrow (a₁ a₂ : Fin 3) : (∑ b : Fin 3, pythRotMat a₁ b * pythRotMat a₂ b) =
        if a₁ = a₂ then 1 else 0 := by
      have h := congrFun (congrFun hR a₁) a₂
      simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using h
    ext l₁ l₂
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_sum_type,
      Fintype.sum_prod_type, Matrix.one_apply]
    rcases l₁ with ⟨v₁, a₁⟩ | ⟨e₁, ⟨a₁, a₂⟩⟩ <;> rcases l₂ with ⟨v₂, d₁⟩ | ⟨e₂, ⟨d₁, d₂⟩⟩
    · simp only [O_blk, mul_zero, Finset.sum_const_zero, add_zero]
      by_cases hv : v₁ = v₂
      · subst hv
        rw [Finset.sum_eq_single v₁]
        · simp [hrow a₁ d₁, Prod.ext_iff]
        · intro v _ hne; simp [hne.symm]
        · simp
      · rw [if_neg (by simp [hv])]
        refine Finset.sum_eq_zero fun v _ => Finset.sum_eq_zero fun b _ => ?_
        by_cases h1 : v = v₁
        · subst h1; simp [Ne.symm hv]
        · simp [Ne.symm h1]
    · simp [O_blk]
    · simp [O_blk]
    · simp only [O_blk, mul_zero, Finset.sum_const_zero, zero_add]
      by_cases he : e₁ = e₂
      · subst he
        rw [Finset.sum_eq_single e₁]
        · simp only [↓reduceIte]
          have hfact : (∑ b₁ : Fin 3, ∑ b₂ : Fin 3,
              (pythRotMat a₁ b₁ * pythRotMat a₂ b₂) * (pythRotMat d₁ b₁ * pythRotMat d₂ b₂)) =
              (∑ b₁ : Fin 3, pythRotMat a₁ b₁ * pythRotMat d₁ b₁) *
                (∑ b₂ : Fin 3, pythRotMat a₂ b₂ * pythRotMat d₂ b₂) := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun b₁ _ => ?_
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun b₂ _ => by ring
          rw [hfact, hrow a₁ d₁, hrow a₂ d₂]
          by_cases h1 : a₁ = d₁ <;> by_cases h2 : a₂ = d₂ <;> simp [h1, h2]
        · intro e _ hne; simp [hne.symm]
        · simp
      · rw [if_neg (by simp [he])]
        refine Finset.sum_eq_zero fun e _ => Finset.sum_eq_zero fun pq _ => ?_
        by_cases h1 : e = e₁
        · subst h1; simp [Ne.symm he]
        · simp [Ne.symm h1]
  rw [show pythShellMap n = fun u => O_blk *ᵥ u from funext hmul_eq]
  exact measurePreserving_pi_gaussian_orthogonal O_blk hO_left hO_right

private theorem conj_pathHamiltonian_of_onsite_coupling {n : ℕ} (W : Register (n + 2))
    (u : PathShell n)
    (honsite : ∀ (v : Fin (n + 2)) (b : Fin 3),
      W * finitePauliMatrix (onsiteWord v b) * star W =
        ∑ a : Fin 3, ((pythRotMat a b : ℝ) : ℂ) • finitePauliMatrix (onsiteWord v a))
    (hcoupling : ∀ (e : Fin (n + 1)) (b₁ b₂ : Fin 3),
      W * finitePauliMatrix (couplingWord e (b₁, b₂)) * star W =
        ∑ a₁ : Fin 3, ∑ a₂ : Fin 3,
          ((pythRotMat a₁ b₁ * pythRotMat a₂ b₂ : ℝ) : ℂ) •
            finitePauliMatrix (couplingWord e (a₁, a₂))) :
    W * pathHamiltonian u * star W = pathHamiltonian (WithLp.toLp 2 (pythShellMap n u.ofLp)) := by
  rw [pathHamiltonian_eq_sum, pathHamiltonian_eq_sum, Matrix.mul_sum, Matrix.sum_mul]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type]
  refine congrArg₂ (· + ·) ?_ ?_
  · refine Finset.sum_congr rfl fun v _ => ?_
    trans (∑ b : Fin 3, ∑ a : Fin 3,
      (((pythRotMat a b * u (.inl (v, b)) : ℝ) : ℂ) • finitePauliMatrix (onsiteWord v a)))
    · refine Finset.sum_congr rfl fun b _ => ?_
      rw [Matrix.mul_smul, Matrix.smul_mul, show pathWord (.inl (v, b)) = onsiteWord v b from rfl,
        honsite v b, Finset.smul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [smul_smul, Complex.ofReal_mul, mul_comm]
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_smul, ← Complex.ofReal_sum]
      rfl
  · refine Finset.sum_congr rfl fun e _ => ?_
    trans (∑ b₁ : Fin 3, ∑ b₂ : Fin 3, ∑ a₁ : Fin 3, ∑ a₂ : Fin 3,
      (((pythRotMat a₁ b₁ * pythRotMat a₂ b₂ * u (.inr (e, (b₁, b₂))) : ℝ) : ℂ) •
        finitePauliMatrix (couplingWord e (a₁, a₂))))
    · refine Finset.sum_congr rfl fun b₁ _ => Finset.sum_congr rfl fun b₂ _ => ?_
      rw [Matrix.mul_smul, Matrix.smul_mul,
        show pathWord (.inr (e, (b₁, b₂))) = couplingWord e (b₁, b₂) from rfl,
        hcoupling e b₁ b₂, Finset.smul_sum]
      refine Finset.sum_congr rfl fun a₁ _ => ?_
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun a₂ _ => ?_
      rw [smul_smul]
      refine congrArg (· • finitePauliMatrix (couplingWord e (a₁, a₂))) ?_
      push_cast; ring
    · rw [sum4_comm]
      refine Finset.sum_congr rfl fun a₁ _ => Finset.sum_congr rfl fun a₂ _ => ?_
      simp_rw [← Finset.sum_smul, ← Complex.ofReal_sum]
      rfl

private theorem prodPyth_conj_pathHamiltonian {n : ℕ} (u : PathShell n) :
    let W := prodLocalMatrix (fun _ : Fin (n + 2) => pythUnitary)
    W * pathHamiltonian u * star W = pathHamiltonian (WithLp.toLp 2 (pythShellMap n u.ofLp)) := by
  intro W
  have honsite (v : Fin (n + 2)) (b : Fin 3) :
      W * finitePauliMatrix (onsiteWord v b) * star W =
        ∑ a : Fin 3, ((pythRotMat a b : ℝ) : ℂ) • finitePauliMatrix (onsiteWord v a) := by
    rw [prodLocalMatrix_conj_pauli]
    ext x y
    rw [Matrix.sum_apply]
    simp only [prodLocalMatrix]
    rw [← Finset.prod_mul_prod_compl ({v} : Finset (Fin (n + 2))), Finset.prod_singleton]
    have hrest : (∏ s ∈ ({v} : Finset (Fin (n + 2)))ᶜ,
        (pythUnitary * boolPauliOption (onsiteWord v b s) * star pythUnitary) (x s) (y s)) =
        ∏ s ∈ ({v} : Finset (Fin (n + 2)))ᶜ, boolPauliOptionEntry none (x s, y s) := by
      refine Finset.prod_congr rfl fun s hs => ?_
      have hsv : s ≠ v := by simpa using hs
      simp [onsiteWord, hsv, boolPauliOption, boolPauliOptionEntry,
        pythUnitary_mem_unitary.2, Matrix.one_apply]
    have hv_eq : boolPauliOption (onsiteWord v b v) = finiteQubitPauli b := by
      simp [onsiteWord, boolPauliOption]
    rw [hv_eq, pythUnitary_conj_pauli b, hrest, Matrix.sum_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, mul_assoc]
    congr 1
    unfold finitePauliMatrix
    rw [← Finset.prod_mul_prod_compl ({v} : Finset (Fin (n + 2))), Finset.prod_singleton]
    congr 1
    · simp [onsiteWord, boolPauliOptionEntry, boolPauliOption]
    · refine Finset.prod_congr rfl fun s hs => ?_
      have hsv : s ≠ v := by simpa using hs
      simp [onsiteWord, hsv]
  have hcoupling (e : Fin (n + 1)) (b₁ b₂ : Fin 3) :
      W * finitePauliMatrix (couplingWord e (b₁, b₂)) * star W =
        ∑ a₁ : Fin 3, ∑ a₂ : Fin 3,
          ((pythRotMat a₁ b₁ * pythRotMat a₂ b₂ : ℝ) : ℂ) •
            finitePauliMatrix (couplingWord e (a₁, a₂)) := by
    rw [prodLocalMatrix_conj_pauli]
    ext x y
    simp only [prodLocalMatrix, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    let pairSet : Finset (Fin (n + 2)) := {e.castSucc, e.succ}
    have hne_cs : e.castSucc ≠ e.succ := e.castSucc_lt_succ.ne
    rw [← Finset.prod_mul_prod_compl pairSet, Finset.prod_pair hne_cs]
    have hrest : (∏ s ∈ pairSetᶜ,
        (pythUnitary * boolPauliOption (couplingWord e (b₁, b₂) s) * star pythUnitary) (x s) (y s)) =
        ∏ s ∈ pairSetᶜ, boolPauliOptionEntry none (x s, y s) := by
      refine Finset.prod_congr rfl fun s hs => ?_
      simp only [pairSet, Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hs
      simp [couplingWord, hs.1, hs.2, boolPauliOption, boolPauliOptionEntry,
        pythUnitary_mem_unitary.2, Matrix.one_apply]
    have hc1 : boolPauliOption (couplingWord e (b₁, b₂) e.castSucc) = finiteQubitPauli b₁ := by
      simp [couplingWord, boolPauliOption]
    have hc2 : boolPauliOption (couplingWord e (b₁, b₂) e.succ) = finiteQubitPauli b₂ := by
      simp [couplingWord, hne_cs.symm, boolPauliOption]
    rw [hc1, hc2, pythUnitary_conj_pauli b₁, pythUnitary_conj_pauli b₂, hrest,
      Matrix.sum_apply, Matrix.sum_apply, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a₁ _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a₂ _ => ?_
    simp only [Matrix.smul_apply, smul_eq_mul, Complex.ofReal_mul]
    have hfp : finitePauliMatrix (couplingWord e (a₁, a₂)) x y =
        finiteQubitPauli a₁ (x e.castSucc) (y e.castSucc) *
          finiteQubitPauli a₂ (x e.succ) (y e.succ) *
          ∏ s ∈ pairSetᶜ, boolPauliOptionEntry none (x s, y s) := by
      unfold finitePauliMatrix
      rw [← Finset.prod_mul_prod_compl pairSet, Finset.prod_pair hne_cs]
      congr 1; congr 1
      · simp [couplingWord, boolPauliOptionEntry, boolPauliOption]
      · simp [couplingWord, hne_cs.symm, boolPauliOptionEntry, boolPauliOption]
      · refine Finset.prod_congr rfl fun s hs => ?_
        simp only [pairSet, Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hs
        simp [couplingWord, hs.1, hs.2]
    rw [hfp]; ring
  exact conj_pathHamiltonian_of_onsite_coupling W u honsite hcoupling

private def kronTwoQubit (R : Matrix Bool Bool ℂ) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  fun p q => R p.1 q.1 * R p.2 q.2

private theorem kronTwoQubit_mem_unitary {R : Matrix Bool Bool ℂ}
    (hR : star R * R = 1 ∧ R * star R = 1) :
    kronTwoQubit R ∈ Matrix.unitaryGroup (Bool × Bool) ℂ := by
  rw [Unitary.mem_iff]
  have hst : star (kronTwoQubit R) =
      fun p q => (star R) p.1 q.1 * (star R) p.2 q.2 := by
    ext p q; simp [kronTwoQubit, star_mul']
  rw [hst]
  constructor <;> ext ⟨p₁, p₂⟩ ⟨q₁, q₂⟩ <;> simp only [kronTwoQubit, Matrix.mul_apply,
    Fintype.sum_prod_type, Matrix.one_apply, Prod.ext_iff]
  · have hf : (∑ x : Bool, ∑ y : Bool,
        ((star R) p₁ x * (star R) p₂ y) * (R x q₁ * R y q₂)) =
        ((star R * R) p₁ q₁) * ((star R * R) p₂ q₂) := by
      simp only [Matrix.mul_apply]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ => by ring
    rw [hf, hR.1, Matrix.one_apply, Matrix.one_apply]
    by_cases hp1 : p₁ = q₁ <;> by_cases hp2 : p₂ = q₂ <;> simp [hp1, hp2]
  · have hf : (∑ x : Bool, ∑ y : Bool,
        (R p₁ x * R p₂ y) * ((star R) x q₁ * (star R) y q₂)) =
        ((R * star R) p₁ q₁) * ((R * star R) p₂ q₂) := by
      simp only [Matrix.mul_apply]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ => by ring
    rw [hf, hR.2, Matrix.one_apply, Matrix.one_apply]
    by_cases hp1 : p₁ = q₁ <;> by_cases hp2 : p₂ = q₂ <;> simp [hp1, hp2]

/-- Decomposing `twoQubitLiftMatrix a b hab U` into `16` rank-`1` tensor products of single-site
matrix units gives `W * twoQubitLiftMatrix a b hab U * star W =
twoQubitLiftMatrix a b hab (kronTwoQubit R * U * star (kronTwoQubit R))`
without reindexing `Config N` sums over `splitTwoQubitConfig`. -/
private theorem prodLocal_conj_twoQubitLiftMatrix {N : ℕ} (R : Matrix Bool Bool ℂ)
    (hR : star R * R = 1 ∧ R * star R = 1)
    (a b : Fin N) (hab : a ≠ b) (U : Matrix (Bool × Bool) (Bool × Bool) ℂ) :
    prodLocalMatrix (fun _ : Fin N => R) * twoQubitLiftMatrix a b hab U *
        star (prodLocalMatrix (fun _ : Fin N => R)) =
      twoQubitLiftMatrix a b hab (kronTwoQubit R * U * star (kronTwoQubit R)) := by
  let W := prodLocalMatrix (fun _ : Fin N => R)
  have hlift_apply (M : Matrix (Bool × Bool) (Bool × Bool) ℂ) (u v : Config N) :
      twoQubitLiftMatrix a b hab M u v =
        if ∀ s : Fin N, s ≠ a → s ≠ b → u s = v s then M (u a, u b) (v a, v b) else 0 := by
    dsimp only [twoQubitLiftMatrix, Matrix.reindex_apply, Matrix.submatrix_apply]
    rw [Equiv.symm_symm]
    change (Matrix.kroneckerMap (· * ·) M 1)
      (splitTwoQubitConfig a b hab u) (splitTwoQubitConfig a b hab v) = _
    rw [Matrix.kroneckerMap_apply]
    by_cases hall : ∀ s : Fin N, s ≠ a → s ≠ b → u s = v s
    · rw [if_pos hall]
      have hrest : (splitTwoQubitConfig a b hab u).2 = (splitTwoQubitConfig a b hab v).2 := by
        ext ⟨s, hs⟩
        exact hall s hs.1 hs.2
      rw [hrest, Matrix.one_apply_eq, mul_one]; rfl
    · rw [if_neg hall]
      have hrest_ne : (splitTwoQubitConfig a b hab u).2 ≠ (splitTwoQubitConfig a b hab v).2 := by
        intro heq; apply hall; intro s hsa hsb
        exact congrFun heq ⟨s, hsa, hsb⟩
      rw [Matrix.one_apply_ne hrest_ne, mul_zero]
  let pairSet : Finset (Fin N) := {a, b}
  have hfactor (A B : Matrix Bool Bool ℂ) :
      twoQubitLiftMatrix a b hab (fun p q => A p.1 q.1 * B p.2 q.2) =
        prodLocalMatrix (fun s => if s = a then A else if s = b then B else 1) := by
    ext u v
    rw [hlift_apply]
    dsimp only [prodLocalMatrix]
    rw [← Finset.prod_mul_prod_compl pairSet, Finset.prod_pair hab]
    simp only [↓reduceIte, hab.symm]
    have hrest : (∏ s ∈ pairSetᶜ,
        (if s = a then A else if s = b then B else 1) (u s) (v s)) =
        if ∀ s : Fin N, s ≠ a → s ≠ b → u s = v s then 1 else 0 := by
      have h1 : ∀ s ∈ pairSetᶜ,
          (if s = a then A else if s = b then B else 1) (u s) (v s) =
            if u s = v s then 1 else 0 := by
        intro s hs
        simp only [pairSet, Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hs
        simp [hs.1, hs.2, Matrix.one_apply]
      rw [Finset.prod_congr rfl h1]
      by_cases hall : ∀ s : Fin N, s ≠ a → s ≠ b → u s = v s
      · rw [if_pos hall]
        refine Finset.prod_eq_one fun s hs => ?_
        simp only [pairSet, Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hs
        rw [if_pos (hall s hs.1 hs.2)]
      · rw [if_neg hall]; push Not at hall
        obtain ⟨s, hsa, hsb, hne⟩ := hall
        exact Finset.prod_eq_zero (by simp [pairSet, hsa, hsb]) (if_neg hne)
    rw [hrest]
    split_ifs <;> ring
  have hconj_factor (A B : Matrix Bool Bool ℂ) :
      W * twoQubitLiftMatrix a b hab (fun p q => A p.1 q.1 * B p.2 q.2) * star W =
        twoQubitLiftMatrix a b hab
          (fun p q => (R * A * star R) p.1 q.1 * (R * B * star R) p.2 q.2) := by
    rw [hfactor A B, hfactor (R * A * star R) (R * B * star R)]
    dsimp only [W]
    rw [prodLocalMatrix_star, prodLocalMatrix_mul, prodLocalMatrix_mul]
    congr 1; funext s
    by_cases hsa : s = a
    · simp [hsa]
    · by_cases hsb : s = b
      · simp [hsb]
      · simp [hsa, hsb, mul_one, hR.2]
  let E₁ (p q : Bool) : Matrix Bool Bool ℂ := fun x y => if x = p ∧ y = q then 1 else 0
  have hU_sum : twoQubitLiftMatrix a b hab U =
      ∑ p : Bool × Bool, ∑ q : Bool × Bool,
        U p q • twoQubitLiftMatrix a b hab (fun r s => E₁ p.1 q.1 r.1 s.1 * E₁ p.2 q.2 r.2 s.2) := by
    ext u v
    rw [hlift_apply, Matrix.sum_apply]
    simp_rw [Matrix.sum_apply, Matrix.smul_apply, hlift_apply, smul_eq_mul]
    by_cases hall : ∀ s : Fin N, s ≠ a → s ≠ b → u s = v s
    · simp only [if_pos hall]
      rw [Finset.sum_eq_single (u a, u b)]
      · rw [Finset.sum_eq_single (v a, v b)]
        · simp [E₁]
        · intro q _ hq
          have h0 : E₁ (u a) q.1 (u a) (v a) * E₁ (u b) q.2 (u b) (v b) = 0 := by
            by_cases h1 : v a = q.1
            · have h2 : v b ≠ q.2 := fun h => hq (Prod.ext h1.symm h.symm)
              simp [E₁, h2]
            · simp [E₁, h1]
          rw [h0, mul_zero]
        · simp
      · intro p _ hp
        refine Finset.sum_eq_zero fun q _ => ?_
        have h0 : E₁ p.1 q.1 (u a) (v a) * E₁ p.2 q.2 (u b) (v b) = 0 := by
          by_cases h1 : u a = p.1
          · have h2 : u b ≠ p.2 := fun h => hp (Prod.ext h1.symm h.symm)
            simp [E₁, h2]
          · simp [E₁, h1]
        rw [h0, mul_zero]
      · simp
    · simp [if_neg hall]
  change W * twoQubitLiftMatrix a b hab U * star W = _
  rw [hU_sum, Matrix.mul_sum, Matrix.sum_mul]
  simp_rw [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul, hconj_factor]
  ext u v
  rw [hlift_apply, Matrix.sum_apply]
  simp_rw [Matrix.sum_apply, Matrix.smul_apply, hlift_apply, smul_eq_mul]
  by_cases hall : ∀ s : Fin N, s ≠ a → s ≠ b → u s = v s
  · simp only [if_pos hall]
    have hE1 (p₀ q₀ x₀ z₀ : Bool) :
        (R * E₁ p₀ q₀ * star R) x₀ z₀ = R x₀ p₀ * (star R) q₀ z₀ := by
      simp only [Matrix.mul_apply, Fintype.sum_bool, E₁]
      cases p₀ <;> cases q₀ <;> simp
    have hstR₂ (q : Bool × Bool) :
        (star (kronTwoQubit R)) q (v a, v b) = (star R) q.1 (v a) * (star R) q.2 (v b) := by
      simp [kronTwoQubit, star_mul']
    have hrhs : (kronTwoQubit R * U * star (kronTwoQubit R)) (u a, u b) (v a, v b) =
        ∑ p : Bool × Bool, ∑ q : Bool × Bool,
          U p q * (kronTwoQubit R (u a, u b) p * (star (kronTwoQubit R)) q (v a, v b)) := by
      simp only [Matrix.mul_apply, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
    rw [hrhs]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [hE1, hE1, hstR₂ q]
    dsimp only [kronTwoQubit]
    ring
  · simp [if_neg hall]

private theorem realizes_one_twoQubitLiftMatrix_unitary {N : ℕ} (a b : Fin N) (hab : a ≠ b)
    (V : Matrix.unitaryGroup (Bool × Bool) ℂ) :
    Realizes 1 (twoQubitLiftMatrix a b hab V.val) := by
  let z_loc := scalarSpecialUnitaryPhase V
  let G_loc := scalarSpecialUnitaryRepresentative V
  have hz_unit : star z_loc * z_loc = 1 := scalarSpecialUnitaryPhase_unitary V
  have hznorm : ‖star z_loc‖ = 1 := by
    have hnorm := congrArg norm hz_unit
    have hsq : ‖z_loc‖ * ‖z_loc‖ = 1 := by simpa [norm_mul] using hnorm
    have hz0 : ‖z_loc‖ = 1 := by nlinarith [norm_nonneg z_loc, sq_nonneg (‖z_loc‖ - 1)]
    simpa using hz0
  refine ⟨star z_loc, hznorm, TwoQubitCircuit.singleOn a b hab G_loc, le_rfl, ?_⟩
  rw [TwoQubitCircuit.singleOn_eval]
  have hgate : (twoQubitLift a b hab G_loc : Register N) =
      z_loc • twoQubitLiftMatrix a b hab V.val := by
    ext x y
    simp [G_loc, z_loc, twoQubitLift, twoQubitLiftMatrix,
      specialUnitaryAsUnitary, scalarSpecialUnitaryRepresentative_coe,
      unitaryGroupReindex_coe, Quantum.tensorGate_val,
      Matrix.reindex_apply, Matrix.kronecker, Matrix.smul_apply]
    ring
  rw [hgate, smul_smul, hz_unit, one_smul]

private theorem realizes_conj_prodLocal {N : ℕ} (R : Matrix Bool Bool ℂ)
    (hR : star R * R = 1 ∧ R * star R = 1) {s : ℕ} {U : Register N} (h : Realizes s U) :
    Realizes s (prodLocalMatrix (fun _ : Fin N => R) * U *
      star (prodLocalMatrix (fun _ : Fin N => R))) := by
  obtain ⟨z, hz, C, hC, hU_eq⟩ := h
  have hW_unit := prodLocalMatrix_mem_unitary (fun _ : Fin N => R) (fun _ => hR)
  have hlist : ∀ (W : Register N), star W * W = 1 → W * star W = 1 →
      ∀ L : List (Matrix.unitaryGroup (Config N) ℂ),
        (∀ g ∈ L, Realizes 1 (W * g.val * star W)) →
        Realizes L.length (W * L.prod.val * star W) := by
    intro W hWL hWR L hL
    induction L with
    | nil =>
        rw [List.length_nil, List.prod_nil, OneMemClass.coe_one, mul_one, hWR]
        exact DiagonalSynthesis.Realizes.one N
    | cons g rest ih =>
        have hsplit : W * (g.val * rest.prod.val) * star W =
            (W * g.val * star W) * (W * rest.prod.val * star W) := by
          calc W * (g.val * rest.prod.val) * star W
              = W * g.val * (star W * W) * rest.prod.val * star W := by
                  rw [hWL, mul_one]; simp only [mul_assoc]
            _ = (W * g.val * star W) * (W * rest.prod.val * star W) := by simp only [mul_assoc]
        rw [List.length_cons, Nat.add_comm, List.prod_cons, Submonoid.coe_mul, hsplit]
        exact DiagonalSynthesis.Realizes.mul
          (hL g (List.mem_cons.mpr (Or.inl rfl)))
          (ih fun x hx => hL x (List.mem_cons.mpr (Or.inr hx)))
  have hR₂_unit : kronTwoQubit R ∈ Matrix.unitaryGroup (Bool × Bool) ℂ :=
    kronTwoQubit_mem_unitary hR
  let L_gates : List (Matrix.unitaryGroup (Config N) ℂ) :=
    (List.ofFn fun r => C.architecture.gateLift r (C.gates r)).reverse
  have hlen : L_gates.length = C.gateCount := by simp [L_gates]
  have hprod_eq : L_gates.prod = C.eval := rfl
  have hmem : ∀ g ∈ L_gates,
      Realizes 1 (prodLocalMatrix (fun _ : Fin N => R) * g.val *
        star (prodLocalMatrix (fun _ : Fin N => R))) := by
    intro g hg
    rw [List.mem_reverse] at hg
    refine ((List.forall_mem_ofFn_iff
      (P := fun g : Matrix.unitaryGroup (Config N) ℂ =>
        Realizes 1 (prodLocalMatrix (fun _ : Fin N => R) * g.val *
          star (prodLocalMatrix (fun _ : Fin N => R))))).mpr fun r => ?_) g hg
    let a := (C.architecture.sites r).1
    let b := (C.architecture.sites r).2
    let hab := C.architecture.distinct r
    let G0 := C.gates r
    have hlift_val : (C.architecture.gateLift r G0).val =
        twoQubitLiftMatrix a b hab (specialUnitaryAsUnitary G0).val := by
      ext x y
      simp only [TwoQubitArchitecture.gateLift, twoQubitLift, twoQubitLiftMatrix,
        unitaryGroupReindex_coe, Quantum.tensorGate_val, OneMemClass.coe_one,
        Matrix.kronecker, Matrix.reindex_apply, Matrix.submatrix_apply, a, b, G0]
    rw [hlift_val, prodLocal_conj_twoQubitLiftMatrix R hR a b hab]
    exact realizes_one_twoQubitLiftMatrix_unitary a b hab
      ⟨kronTwoQubit R * (specialUnitaryAsUnitary G0).val * star (kronTwoQubit R),
        mul_mem (mul_mem hR₂_unit (specialUnitaryAsUnitary G0).2) (Unitary.star_mem hR₂_unit)⟩
  obtain ⟨hWL, hWR⟩ := Unitary.mem_iff.mp hW_unit
  have hcirc : Realizes C.gateCount
      (prodLocalMatrix (fun _ : Fin N => R) * C.eval.val *
        star (prodLocalMatrix (fun _ : Fin N => R))) := by
    rw [← hlen, ← hprod_eq]
    exact hlist _ hWL hWR L_gates hmem
  obtain ⟨z', hz', C', hC', heq'⟩ := hcirc
  refine ⟨z * z', by rw [norm_mul, hz, hz', mul_one], C', hC'.trans hC, ?_⟩
  rw [hU_eq, Matrix.mul_smul, Matrix.smul_mul, heq', smul_smul]

private theorem realizes_conj_pyth {N : ℕ} {s : ℕ} {U : Register N} (h : Realizes s U) :
    let W := prodLocalMatrix (fun _ : Fin N => pythUnitary)
    Realizes s (W * U * star W) :=
  realizes_conj_prodLocal pythUnitary pythUnitary_mem_unitary h

private theorem pythShellMap_allCoordStrong {n : ℕ} {η M_η δ : ℝ}
    (hM_ge18 : 18 ≤ M_η) (hM_ge_eta : 9 * |η| + 18 ≤ M_η) (hδ_le_small : δ ≤ 1 / 200)
    {u_tilde : PathLabel n → ℝ}
    (hdiag : ∀ l : PathLabel n, IsDiagLabel l → M_η ≤ u_tilde l)
    (hoff : ∀ l : PathLabel n, ¬ IsDiagLabel l → |u_tilde l| ≤ δ) :
    (fun i => pythShellMap n u_tilde (pathCoeffEquiv n i)) ∈ allCoordStrongEvent n η ∧
    3 ≤ |pythShellMap n u_tilde (.inl (0, 2))| := by
  have hcol2_ge (a : Fin 3) : 1 / 3 ≤ pythRotMat a 2 := by
    fin_cases a <;> simp [pythRotMat] <;> norm_num
  have hentry_abs_le (a b : Fin 3) : |pythRotMat a b| ≤ 1 := by
    fin_cases a <;> fin_cases b <;> simp [pythRotMat] <;> norm_num
  have h_eta_le : η ≤ |η| := le_abs_self η
  refine ⟨fun i => ?_, ?_⟩
  · change η ≤ |pythShellMap n u_tilde (pathCoeffEquiv n i)|
    rcases pathCoeffEquiv n i with ⟨v, a⟩ | ⟨e, ⟨a₁, a₂⟩⟩
    · have hz_ge : M_η ≤ u_tilde (.inl (v, 2)) := hdiag (.inl (v, 2)) rfl
      have hx_in : |u_tilde (.inl (v, 0))| ≤ δ := hoff (.inl (v, 0)) (by simp [IsDiagLabel])
      have hy_in : |u_tilde (.inl (v, 1))| ≤ δ := hoff (.inl (v, 1)) (by simp [IsDiagLabel])
      have hval_eq : pythShellMap n u_tilde (.inl (v, a)) =
          pythRotMat a 0 * u_tilde (.inl (v, 0)) +
          pythRotMat a 1 * u_tilde (.inl (v, 1)) +
          pythRotMat a 2 * u_tilde (.inl (v, 2)) := by
        simp [pythShellMap, Fin.sum_univ_three]
      have h0_bd : -δ ≤ pythRotMat a 0 * u_tilde (.inl (v, 0)) := by
        have h := mul_le_mul (hentry_abs_le a 0) hx_in (abs_nonneg _) zero_le_one
        rw [← abs_mul, one_mul] at h; exact (abs_le.mp h).1
      have h1_bd : -δ ≤ pythRotMat a 1 * u_tilde (.inl (v, 1)) := by
        have h := mul_le_mul (hentry_abs_le a 1) hy_in (abs_nonneg _) zero_le_one
        rw [← abs_mul, one_mul] at h; exact (abs_le.mp h).1
      have h2_bd : (1 / 3 : ℝ) * M_η ≤ pythRotMat a 2 * u_tilde (.inl (v, 2)) :=
        mul_le_mul (hcol2_ge a) hz_ge (by linarith only [hM_ge18]) (le_trans (by norm_num) (hcol2_ge a))
      have hpos_val : η ≤ pythShellMap n u_tilde (.inl (v, a)) := by
        linarith only [hval_eq, h0_bd, h1_bd, h2_bd, hδ_le_small, hM_ge_eta, h_eta_le, abs_nonneg η]
      exact hpos_val.trans (le_abs_self _)
    · have hzz_ge : M_η ≤ u_tilde (.inr (e, (2, 2))) := hdiag (.inr (e, (2, 2))) rfl
      have hoff_bd (pq : Fin 3 × Fin 3) (hpq : pq ≠ (2, 2)) :
          -δ ≤ pythRotMat a₁ pq.1 * pythRotMat a₂ pq.2 * u_tilde (.inr (e, pq)) := by
        have hu_le : |u_tilde (.inr (e, pq))| ≤ δ := hoff (.inr (e, pq)) hpq
        have hc_le : |pythRotMat a₁ pq.1 * pythRotMat a₂ pq.2| ≤ 1 := by
          rw [abs_mul]
          exact (mul_le_mul (hentry_abs_le a₁ pq.1) (hentry_abs_le a₂ pq.2)
            (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
        have h := mul_le_mul hc_le hu_le (abs_nonneg _) zero_le_one
        rw [← abs_mul, one_mul] at h
        exact (abs_le.mp h).1
      have hzz_bd : (1 / 9 : ℝ) * M_η ≤
          pythRotMat a₁ 2 * pythRotMat a₂ 2 * u_tilde (.inr (e, (2, 2))) := by
        have hc9 : (1 / 9 : ℝ) ≤ pythRotMat a₁ 2 * pythRotMat a₂ 2 := by
          have h1 := hcol2_ge a₁; have h2 := hcol2_ge a₂
          nlinarith only [h1, h2]
        exact mul_le_mul hc9 hzz_ge (by linarith only [hM_ge18]) (by linarith only [hc9])
      have hsum_split : pythShellMap n u_tilde (.inr (e, (a₁, a₂))) =
          pythRotMat a₁ 2 * pythRotMat a₂ 2 * u_tilde (.inr (e, (2, 2))) +
            ∑ pq ∈ (Finset.univ : Finset (Fin 3 × Fin 3)).erase (2, 2),
              pythRotMat a₁ pq.1 * pythRotMat a₂ pq.2 * u_tilde (.inr (e, pq)) := by
        dsimp only [pythShellMap]
        rw [← Fintype.sum_prod_type (f := fun pq : Fin 3 × Fin 3 =>
          pythRotMat a₁ pq.1 * pythRotMat a₂ pq.2 * u_tilde (.inr (e, pq)))]
        exact (Finset.add_sum_erase Finset.univ _ (Finset.mem_univ ((2 : Fin 3), (2 : Fin 3)))).symm
      have herase_ge : -8 * δ ≤
          ∑ pq ∈ (Finset.univ : Finset (Fin 3 × Fin 3)).erase (2, 2),
            pythRotMat a₁ pq.1 * pythRotMat a₂ pq.2 * u_tilde (.inr (e, pq)) := by
        have hcard8 : ((Finset.univ : Finset (Fin 3 × Fin 3)).erase (2, 2)).card = 8 := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
            Fintype.card_prod, Fintype.card_fin]
        calc -8 * δ
            = ∑ _pq ∈ (Finset.univ : Finset (Fin 3 × Fin 3)).erase (2, 2), (-δ) := by
                rw [Finset.sum_const, hcard8, nsmul_eq_mul]; ring
          _ ≤ _ := Finset.sum_le_sum fun pq hpq => hoff_bd pq (Finset.ne_of_mem_erase hpq)
      have hpos_val : η ≤ pythShellMap n u_tilde (.inr (e, (a₁, a₂))) := by
        linarith only [hsum_split, hzz_bd, herase_ge, hδ_le_small, hM_ge_eta, h_eta_le]
      exact hpos_val.trans (le_abs_self _)
  · have hz_ge : M_η ≤ u_tilde (.inl (0, 2)) := hdiag (.inl (0, 2)) rfl
    have hx_bd := (abs_le.mp (hoff (.inl (0, 0)) (by simp [IsDiagLabel]))).2
    have hy_bd := (abs_le.mp (hoff (.inl (0, 1)) (by simp [IsDiagLabel]))).2
    have hval_eq : pythShellMap n u_tilde (.inl (0, 2)) =
        (-2 / 3 : ℝ) * u_tilde (.inl (0, 0)) + (-2 / 3 : ℝ) * u_tilde (.inl (0, 1)) +
          (1 / 3 : ℝ) * u_tilde (.inl (0, 2)) := by
      simp [pythShellMap, Fin.sum_univ_three, pythRotMat]
    have hge : 3 ≤ pythShellMap n u_tilde (.inl (0, 2)) := by
      linarith only [hval_eq, hx_bd, hy_bd, hz_ge, hM_ge18, hδ_le_small]
    exact hge.trans (le_abs_self _)

/-- Hidden locally rotated Ising survival tube **strictly inside `allCoordStrongEvent (k + 1) η ⊆
uniformClawEvent (k + 1) η ⊆ twoCutConnectedEvent (k + 1) η`**: for every `η : ℝ` and all
sufficiently large `k` (`N = k + 3`), there is `c > 0` such that for every `T ≥ 2`, an event of
`pathPauliDisorderLaw` probability `≥ c * T ^ -(10 * k + 22)` simultaneously satisfies:
1. `x ∈ allCoordStrongEvent (k + 1) η ⊆ uniformClawEvent (k + 1) η`,
2. maximally projective simple spectrum, full `2^N` Vandermonde rank on `[0, 1]`, and `√2`
   scalar-return excision, yet
3. `T < tenthPlateauOnset H s` for **every** budget `k + 2 ≤ s ≤ P` (`N - 1 ≤ s ≤ P`). -/
theorem gaussian_hiddenRotatedIsing_claw_tube_tail (η : ℝ) :
    ∀ᶠ k : ℕ in atTop,
      let N := k + 3
      let P := nearHilbertContinuousCircuitBudget N
      ∃ c : ℝ, 0 < c ∧ ∀ T : ℝ, 2 ≤ T →
        c ≤ T ^ (10 * k + 22) * pathPauliDisorderLaw.real {ω : PathPauliDisorder |
          let u := pathPauliDisorderShell ω (k + 1)
          let x : PrefixIndex (k + 1) → ℝ := fun i => u (pathCoeffEquiv (k + 1) i)
          let H : selfAdjoint (Register N) := ⟨pathHamiltonian u, isSelfAdjoint_pathHamiltonian u⟩
          x ∈ allCoordStrongEvent (k + 1) η ∧
          x ∈ uniformClawEvent (k + 1) η ∧
          MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues ∧
          (∃ τ > 0, (∀ m : Fin (2 ^ N), ((m : ℕ) : ℝ) * τ ∈ Icc (0 : ℝ) 1) ∧
            Module.finrank ℂ (Submodule.span ℂ
              (range fun m : Fin (2 ^ N) => unitaryEvolution H.val (((m : ℕ) : ℝ) * τ))) = 2 ^ N) ∧
          (∃ t₀ ∈ Ioc (0 : ℝ) T, ∀ z : ℂ, ‖z‖ = 1 →
            Real.sqrt 2 ≤ ‖unitaryEvolution H.val t₀ - z • (1 : Register N)‖) ∧
          (∀ s : ℕ, k + 2 ≤ s → s ≤ P → T < tenthPlateauOnset H s)} := by
  letI : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance
  let γ := gaussianReal 0 1
  have hent := (tendsto_add_atTop_nat 3).eventually
    eventually_nearHilbertContinuousCircuitEntropy_lt_projectiveBooleanCarrier
  filter_upwards [hent, eventually_ge_atTop 16] with k hentropy hklarge
  intro N P
  have hP_ge : 2 * (k + 2) ≤ P := by
    dsimp only [P, N, nearHilbertContinuousCircuitBudget]
    have hind : ∀ m : ℕ, 16 ≤ m → 64 * (m + 4) * (2 * (m + 2)) ≤ 2 ^ (m + 3) := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base => norm_num
      | succ m hm ih =>
          calc 64 * (m + 5) * (2 * (m + 3))
              ≤ 2 * (64 * (m + 4) * (2 * (m + 2))) := by nlinarith only [hm]
            _ ≤ 2 * 2 ^ (m + 3) := Nat.mul_le_mul_left 2 ih
            _ = 2 ^ (m + 4) := by rw [← pow_succ']
    exact (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [mul_comm]; exact hind k hklarge)
  let M_η : ℝ := 9 * max |η| 0 + 18
  have hM_ge18 : 18 ≤ M_η := by dsimp [M_η]; linarith [le_max_right |η| 0]
  have hM_ge_eta : 9 * |η| + 18 ≤ M_η := by dsimp [M_η]; linarith [le_max_left |η| 0]
  let diagEmb : Fin (2 * (k + 1) + 3) ↪ PathLabel (k + 1) :=
    ⟨fun i => pathPatchEquiv (k + 1) (.inl i),
     fun _ _ h => Sum.inl.inj ((pathPatchEquiv (k + 1)).injective h)⟩
  let offEmb : Fin (10 * (k + 1) + 12) ↪ PathLabel (k + 1) :=
    ⟨fun j => pathPatchEquiv (k + 1) (.inr j),
     fun _ _ h => Sum.inr.inj ((pathPatchEquiv (k + 1)).injective h)⟩
  let S_diag : Finset (PathLabel (k + 1)) := Finset.univ.map diagEmb
  let S_weak : Finset (PathLabel (k + 1)) := Finset.univ.map offEmb
  have hcard_d : S_diag.card = 2 * k + 5 := by
    simp only [S_diag, Finset.card_map, Finset.card_univ, Fintype.card_fin]; omega
  have hcard_w : S_weak.card = 10 * k + 22 := by
    simp only [S_weak, Finset.card_map, Finset.card_univ, Fintype.card_fin]; omega
  have hdisj : Disjoint S_diag S_weak := by
    refine Finset.disjoint_left.mpr fun l hld hlw => ?_
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hld
    obtain ⟨j, _, heq⟩ := Finset.mem_map.mp hlw
    exact notDiag_pathPatchEquiv_inr j (heq ▸ isDiag_pathPatchEquiv_inl i)
  have hunion_univ : S_diag ∪ S_weak = Finset.univ := by
    ext l
    simp only [Finset.mem_union, S_diag, S_weak, Finset.mem_map, Finset.mem_univ, true_and,
      iff_true, diagEmb, offEmb, Function.Embedding.coeFn_mk]
    rcases hp : (pathPatchEquiv (k + 1)).symm l with i | j
    · left; exact ⟨i, (pathPatchEquiv (k + 1)).eq_symm_apply.mp hp.symm⟩
    · right; exact ⟨j, (pathPatchEquiv (k + 1)).eq_symm_apply.mp hp.symm⟩
  have hdiag_mem_iff (l : PathLabel (k + 1)) : l ∈ S_diag ↔ IsDiagLabel l := by
    constructor
    · intro hl; obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hl
      exact isDiag_pathPatchEquiv_inl i
    · intro hd
      rcases hp : (pathPatchEquiv (k + 1)).symm l with i | j
      · exact Finset.mem_map.mpr ⟨i, Finset.mem_univ i,
          (pathPatchEquiv (k + 1)).eq_symm_apply.mp hp.symm⟩
      · exfalso
        have h := (pathPatchEquiv (k + 1)).eq_symm_apply.mp hp.symm
        exact notDiag_pathPatchEquiv_inr j (h ▸ hd)
  have hp_diag : 0 < γ.real (Icc M_η (M_η + 1)) :=
    ENNReal.toReal_pos (gaussianReal_Icc_pos (by linarith)).ne' (measure_ne_top _ _)
  let W_num : ℝ := 100 * ((10 * k + 22 : ℕ) : ℝ)
  have hW_pos : 0 < W_num := by dsimp only [W_num]; positivity
  let c : ℝ := (γ.real (Icc M_η (M_η + 1))) ^ (2 * k + 5) *
    (2 * gaussianDensityFloor / W_num) ^ (10 * k + 22)
  have hc_pos : 0 < c :=
    mul_pos (pow_pos hp_diag _)
      (pow_pos (div_pos (mul_pos two_pos gaussianDensityFloor_pos) hW_pos) _)
  refine ⟨c, hc_pos, fun T hT2 => ?_⟩
  have hT_pos : 0 < T := by linarith only [hT2]
  let δ : ℝ := 1 / (W_num * T)
  have hδ_pos : 0 < δ := div_pos zero_lt_one (mul_pos hW_pos hT_pos)
  have hδ_le_small : δ ≤ 1 / 200 := by
    have hW1 : 100 ≤ W_num := by
      dsimp only [W_num]
      have : (1 : ℝ) ≤ ((10 * k + 22 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ 10 * k + 22 by omega)
      linarith only [this]
    rw [div_le_div_iff₀ (mul_pos hW_pos hT_pos) (by norm_num)]
    nlinarith only [hW1, hT2]
  let F_coord : PathLabel (k + 1) → Set ℝ := fun l =>
    if l ∈ S_diag then Icc M_η (M_η + 1) else Icc (-δ) δ
  let RotBox : Set (PathLabel (k + 1) → ℝ) := Set.univ.pi F_coord
  have hRotBox_meas : MeasurableSet RotBox :=
    MeasurableSet.pi (Set.to_countable _) fun l _ => by
      dsimp only [F_coord]; split_ifs <;> exact measurableSet_Icc
  have hRotBox_mass : (γ.real (Icc M_η (M_η + 1))) ^ (2 * k + 5) *
      (2 * gaussianDensityFloor * δ) ^ (10 * k + 22) ≤
      (Measure.pi fun _ : PathLabel (k + 1) => γ).real RotBox := by
    have hprod_eq : (Measure.pi fun _ : PathLabel (k + 1) => γ).real RotBox =
        (∏ l ∈ S_diag, γ.real (F_coord l)) * (∏ l ∈ S_weak, γ.real (F_coord l)) := by
      rw [Measure.real_def, Measure.pi_pi, ENNReal.toReal_prod, ← hunion_univ,
        Finset.prod_union hdisj]; rfl
    have hpd : (∏ l ∈ S_diag, γ.real (F_coord l)) = (γ.real (Icc M_η (M_η + 1))) ^ (2 * k + 5) := by
      have h1 : (∏ l ∈ S_diag, γ.real (F_coord l)) = ∏ _l ∈ S_diag, γ.real (Icc M_η (M_η + 1)) :=
        Finset.prod_congr rfl fun l hl => by simp [F_coord, hl]
      rw [h1, Finset.prod_const, hcard_d]
    have hpw : (∏ l ∈ S_weak, γ.real (F_coord l)) = (γ.real (Icc (-δ) δ)) ^ (10 * k + 22) := by
      have h1 (l : PathLabel (k + 1)) (hl : l ∈ S_weak) : l ∉ S_diag :=
        Finset.disjoint_right.mp hdisj hl
      have h2 : (∏ l ∈ S_weak, γ.real (F_coord l)) = ∏ _l ∈ S_weak, γ.real (Icc (-δ) δ) :=
        Finset.prod_congr rfl fun l hl => by simp [F_coord, h1 l hl]
      rw [h2, Finset.prod_const, hcard_w]
    have hlow_enn := ENNReal.toReal_mono (measure_ne_top γ (Icc (-δ) δ))
      (gaussianReal_Icc_lower (hδ_le_small.trans (by norm_num)))
    rw [ENNReal.toReal_ofReal (mul_nonneg gaussianDensityFloor_pos.le (by linarith only [hδ_pos])),
      ← Measure.real_def] at hlow_enn
    have h1d : 2 * gaussianDensityFloor * δ ≤ γ.real (Icc (-δ) δ) := by linarith only [hlow_enn]
    rw [hprod_eq, hpd, hpw]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (mul_nonneg (mul_nonneg two_pos.le gaussianDensityFloor_pos.le) hδ_pos.le) h1d _)
      (pow_nonneg measureReal_nonneg _)
  let PhysTube : Set (PathLabel (k + 1) → ℝ) := pythShellInv (k + 1) ⁻¹' RotBox
  have hPhysTube_meas : MeasurableSet PhysTube := by
    have hm_inv : Measurable (pythShellInv (k + 1)) := by
      refine measurable_pi_lambda _ fun l => ?_
      rcases l with ⟨v, b⟩ | ⟨e, ⟨b₁, b₂⟩⟩
      · exact Finset.measurable_sum _ fun a _ => measurable_const.mul (measurable_pi_apply _)
      · exact Finset.measurable_sum _ fun a₁ _ => Finset.measurable_sum _ fun a₂ _ =>
          measurable_const.mul (measurable_pi_apply _)
    exact hRotBox_meas.preimage hm_inv
  have hPhysTube_mass : (Measure.pi fun _ : PathLabel (k + 1) => γ).real PhysTube =
      (Measure.pi fun _ : PathLabel (k + 1) => γ).real RotBox := by
    have hpre := (pythShellMap_measurePreserving (k + 1)).measure_preimage
      hPhysTube_meas.nullMeasurableSet
    have heq_set : pythShellMap (k + 1) ⁻¹' PhysTube = RotBox := by
      ext z; change pythShellInv (k + 1) (pythShellMap (k + 1) z) ∈ RotBox ↔ z ∈ RotBox
      rw [pythShellInv_left]
    rw [heq_set] at hpre
    exact (congrArg ENNReal.toReal hpre).symm
  let u_map : PathPauliDisorder → PathLabel (k + 1) → ℝ :=
    fun ω l => pathPauliDisorderShell ω (k + 1) l
  have hmp_lbl := measurePreserving_pathDisorder_labels (k + 1)
  have hpre_mass : pathPauliDisorderLaw.real (u_map ⁻¹' PhysTube) =
      (Measure.pi fun _ : PathLabel (k + 1) => γ).real RotBox :=
    (congrArg ENNReal.toReal (hmp_lbl.measure_preimage hPhysTube_meas.nullMeasurableSet)).trans
      hPhysTube_mass
  let TargetEvent : Set PathPauliDisorder := {ω : PathPauliDisorder |
    let u := pathPauliDisorderShell ω (k + 1)
    let x : PrefixIndex (k + 1) → ℝ := fun i => u (pathCoeffEquiv (k + 1) i)
    let H : selfAdjoint (Register N) := ⟨pathHamiltonian u, isSelfAdjoint_pathHamiltonian u⟩
    x ∈ allCoordStrongEvent (k + 1) η ∧
    x ∈ uniformClawEvent (k + 1) η ∧
    MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues ∧
    (∃ τ > 0, (∀ m : Fin (2 ^ N), ((m : ℕ) : ℝ) * τ ∈ Icc (0 : ℝ) 1) ∧
      Module.finrank ℂ (Submodule.span ℂ
        (range fun m : Fin (2 ^ N) => unitaryEvolution H.val (((m : ℕ) : ℝ) * τ))) = 2 ^ N) ∧
    (∃ t₀ ∈ Ioc (0 : ℝ) T, ∀ z : ℂ, ‖z‖ = 1 →
      Real.sqrt 2 ≤ ‖unitaryEvolution H.val t₀ - z • (1 : Register N)‖) ∧
    (∀ s : ℕ, k + 2 ≤ s → s ≤ P → T < tenthPlateauOnset H s)}
  have hae_sub : u_map ⁻¹' PhysTube ≤ᵐ[pathPauliDisorderLaw] TargetEvent := by
    filter_upwards [gaussian_path_all_prefixes_maximally_projective] with ω hmax_all hω_in
    let u := pathPauliDisorderShell ω (k + 1)
    let u_tilde : PathShell (k + 1) := WithLp.toLp 2 (pythShellInv (k + 1) u.ofLp)
    have hu_ofLp : u.ofLp = pythShellMap (k + 1) u_tilde.ofLp :=
      (pythShellInv_right (k + 1) u.ofLp).symm
    have hu_eq : u = WithLp.toLp 2 (pythShellMap (k + 1) u_tilde.ofLp) :=
      WithLp.ofLp_injective 2 hu_ofLp
    have htilde_box : ∀ l : PathLabel (k + 1), u_tilde l ∈ F_coord l := fun l =>
      hω_in l (mem_univ l)
    have hdiag_ge : ∀ l : PathLabel (k + 1), IsDiagLabel l → M_η ≤ u_tilde.ofLp l := fun l hd => by
      have h := htilde_box l
      rw [show F_coord l = Icc M_η (M_η + 1) from if_pos ((hdiag_mem_iff l).mpr hd)] at h
      exact h.1
    have hoff_le : ∀ l : PathLabel (k + 1), ¬ IsDiagLabel l → |u_tilde.ofLp l| ≤ δ := fun l hnd => by
      have hnot : l ∉ S_diag := fun h => hnd ((hdiag_mem_iff l).mp h)
      exact abs_le.mpr (by simpa only [F_coord, if_neg hnot, Set.mem_Icc] using htilde_box l)
    obtain ⟨hall_map, hz0_map⟩ := pythShellMap_allCoordStrong hM_ge18 hM_ge_eta hδ_le_small
      hdiag_ge hoff_le
    have hall_coord : (fun i => u (pathCoeffEquiv (k + 1) i)) ∈ allCoordStrongEvent (k + 1) η := by
      simpa only [← hu_ofLp] using hall_map
    have hz0_ge3 : 3 ≤ |u (.inl (0, 2))| := by
      simpa only [← hu_ofLp] using hz0_map
    let H : selfAdjoint (Register N) := ⟨pathHamiltonian u, isSelfAdjoint_pathHamiltonian u⟩
    have hmax : MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues := hmax_all k
    have hvand := vandermonde_full_rank_unit_interval H hmax.injective
    let W_pyth : Register N := prodLocalMatrix (fun _ : Fin N => pythUnitary)
    have hW_unit : W_pyth ∈ unitary (Register N) :=
      prodLocalMatrix_mem_unitary _ fun _ => pythUnitary_mem_unitary
    have hH_conj : W_pyth * pathHamiltonian u_tilde * star W_pyth = H.val := by
      change W_pyth * pathHamiltonian u_tilde * star W_pyth = pathHamiltonian u
      rw [prodPyth_conj_pathHamiltonian u_tilde, ← hu_eq]
    have hev_conj (t : ℝ) :
        unitaryEvolution H.val t = W_pyth * unitaryEvolution (pathHamiltonian u_tilde) t * star W_pyth := by
      let W_ug : Matrix.unitaryGroup (Config N) ℂ := ⟨W_pyth, hW_unit⟩
      have hu_unit := Unitary.isUnit_coe (U := W_ug)
      have hc := unitaryEvolution_conj W_pyth (pathHamiltonian u_tilde) hu_unit t
      rw [inv_eq_star_of_mem_unitary hW_unit, hH_conj] at hc
      exact hc
    have hexc := exists_antipodal_return_excision_of_shell_coeff u (.inl (0, 2)) hz0_ge3 hT2
    let u_tilde_diag : PathShell (k + 1) :=
      WithLp.toLp 2 fun l => if IsDiagLabel l then u_tilde l else 0
    have htilde_diag_off : ∀ l : PathLabel (k + 1), ¬ IsDiagLabel l → u_tilde_diag l = 0 :=
      fun l hl => if_neg hl
    have hdiff_tilde : ‖pathHamiltonian u_tilde - pathHamiltonian u_tilde_diag‖ ≤
        ((10 * k + 22 : ℕ) : ℝ) * δ := by
      have hsub_sum : pathHamiltonian u_tilde - pathHamiltonian u_tilde_diag =
          ∑ j : Fin (10 * (k + 1) + 12),
            ((u_tilde (pathPatchEquiv (k + 1) (.inr j)) : ℝ) : ℂ) •
              finitePauliMatrix (pathWord (pathPatchEquiv (k + 1) (.inr j))) := by
        rw [pathHamiltonian_eq_sum, pathHamiltonian_eq_sum, ← Finset.sum_sub_distrib,
          ← Equiv.sum_comp (pathPatchEquiv (k + 1)), Fintype.sum_sum_type]
        have hinl : ∑ i : Fin (2 * (k + 1) + 3),
            (((u_tilde (pathPatchEquiv (k + 1) (.inl i)) : ℝ) : ℂ) •
              finitePauliMatrix (pathWord (pathPatchEquiv (k + 1) (.inl i))) -
             ((u_tilde_diag (pathPatchEquiv (k + 1) (.inl i)) : ℝ) : ℂ) •
              finitePauliMatrix (pathWord (pathPatchEquiv (k + 1) (.inl i)))) = 0 := by
          refine Finset.sum_eq_zero fun i _ => ?_
          have hd := isDiag_pathPatchEquiv_inl (n := k + 1) i
          have heq : u_tilde_diag (pathPatchEquiv (k + 1) (.inl i)) =
              u_tilde (pathPatchEquiv (k + 1) (.inl i)) := if_pos hd
          rw [heq, sub_self]
        rw [hinl, zero_add]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hnd := notDiag_pathPatchEquiv_inr (n := k + 1) j
        have heq0 : u_tilde_diag (pathPatchEquiv (k + 1) (.inr j)) = 0 := if_neg hnd
        rw [heq0, Complex.ofReal_zero, zero_smul, sub_zero]
      rw [hsub_sum]
      refine (norm_sum_le _ _).trans ?_
      have hterm (j : Fin (10 * (k + 1) + 12)) :
          ‖((u_tilde (pathPatchEquiv (k + 1) (.inr j)) : ℝ) : ℂ) •
            finitePauliMatrix (pathWord (pathPatchEquiv (k + 1) (.inr j)))‖ ≤ δ := by
        rw [norm_smul, norm_finitePauliMatrix, mul_one, Complex.norm_real, Real.norm_eq_abs]
        exact hoff_le _ (notDiag_pathPatchEquiv_inr j)
      calc ∑ j : Fin (10 * (k + 1) + 12),
              ‖((u_tilde (pathPatchEquiv (k + 1) (.inr j)) : ℝ) : ℂ) •
                finitePauliMatrix (pathWord (pathPatchEquiv (k + 1) (.inr j)))‖
          ≤ ∑ _j : Fin (10 * (k + 1) + 12), δ := Finset.sum_le_sum fun j _ => hterm j
        _ = ((10 * k + 22 : ℕ) : ℝ) * δ := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; rfl
    have hearly_inc (t : ℝ) (ht : |t| ≤ T) :
        HasProjectiveCircuitApproximation N (1 / 100 : ℝ) (k + 2)
          (unitaryEvolution H.val t) := by
      have hreal_rot := realizes_conj_pyth
        (realizes_one_gate_per_bond_of_isDiag u_tilde_diag htilde_diag_off t)
      obtain ⟨z, hz, C, hC, hU_rot⟩ := hreal_rot
      refine ⟨z, hz, C, hC, ?_⟩
      rw [← hU_rot, hev_conj t, ← Matrix.sub_mul, ← Matrix.mul_sub,
        l2_opNorm_unitary_conj_eq (V := W_pyth) hW_unit]
      calc ‖unitaryEvolution (pathHamiltonian u_tilde) t -
              unitaryEvolution (pathHamiltonian u_tilde_diag) t‖
          ≤ |t| * ‖pathHamiltonian u_tilde - pathHamiltonian u_tilde_diag‖ :=
            norm_unitaryEvolution_sub_le _ _ (isSelfAdjoint_pathHamiltonian u_tilde)
              (isSelfAdjoint_pathHamiltonian u_tilde_diag) t
        _ ≤ T * (((10 * k + 22 : ℕ) : ℝ) * δ) :=
            mul_le_mul ht hdiff_tilde (norm_nonneg _) hT_pos.le
        _ = 1 / 100 := by dsimp only [δ, W_num]; field_simp [hT_pos.ne', hW_pos.ne']
    let d := 2 ^ N - 1
    let e_fin : Config N ≃ Fin (d + 1) := (Fintype.equivFin _).trans
      (finCongr (by
        simp only [Config, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
        have hd : 0 < 2 ^ N := Nat.two_pow_pos N
        dsimp [d]; omega))
    obtain ⟨σ, hσ_gt, hσ_eq, _, _, _⟩ := first_circuit_threshold_of_increment e_fin H
      (hmax.comp_equiv e_fin.symm) hentropy T hT_pos.le hP_ge hearly_inc
    have honset_gt (s : ℕ) (hs_lo : k + 2 ≤ s) (hs_hi : s ≤ P) :
        T < tenthPlateauOnset H s := by
      have hearly (t : ℝ) (ht : t ∈ Icc 0 T) : orbitCircuitDistance H s t < 1 / 10 := by
        have habs : |t| ≤ T := by rw [abs_of_nonneg ht.1]; exact ht.2
        obtain ⟨z, hz, C, hC, herr⟩ := hearly_inc t habs
        have hd := (hasProjectiveCircuitApproximation_iff_infDist _ s (1 / 100 : ℝ)).mp
          ⟨z, hz, C, hC.trans hs_lo, herr⟩
        change orbitCircuitDistance H s t ≤ 1 / 100 at hd
        linarith only [hd]
      have hB_gt : 1 / 10 < orbitCircuitDistance H s σ := by
        have hmono : orbitCircuitDistance H P σ ≤ orbitCircuitDistance H s σ := by
          apply (hasProjectiveCircuitApproximation_iff_infDist _ P _).mp
          obtain ⟨z, hz, C, hC, herr⟩ := (hasProjectiveCircuitApproximation_iff_infDist _ s _).mpr
            (le_rfl : orbitCircuitDistance H s σ ≤ _)
          exact ⟨z, hz, C, hC.trans hs_hi, herr⟩
        rw [hσ_eq] at hmono
        linarith only [hmono]
      exact (tenthPlateauOnset_spec H hT_pos (hT_pos.trans hσ_gt).le hearly hB_gt).1
    exact ⟨hall_coord, allCoordStrongEvent_subset_uniformClawEvent (k + 1) η hall_coord,
      hmax, hvand, hexc, honset_gt⟩
  have hmeas_le : (Measure.pi fun _ : PathLabel (k + 1) => γ).real RotBox ≤
      pathPauliDisorderLaw.real TargetEvent := by
    rw [← hpre_mass]
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hae_sub)
  have hc_eq : c = T ^ (10 * k + 22) *
      ((γ.real (Icc M_η (M_η + 1))) ^ (2 * k + 5) *
        (2 * gaussianDensityFloor * δ) ^ (10 * k + 22)) := by
    dsimp only [c, δ]
    have hpow_T : T ^ (10 * k + 22) * (2 * gaussianDensityFloor * (1 / (W_num * T))) ^ (10 * k + 22) =
        (2 * gaussianDensityFloor / W_num) ^ (10 * k + 22) := by
      rw [← mul_pow]; congr 1; field_simp [hT_pos.ne', hW_pos.ne']
    calc c = (γ.real (Icc M_η (M_η + 1))) ^ (2 * k + 5) *
            (T ^ (10 * k + 22) * (2 * gaussianDensityFloor * (1 / (W_num * T))) ^ (10 * k + 22)) := by
              dsimp only [c]; rw [hpow_T]
      _ = _ := by ring
  rw [hc_eq]
  exact mul_le_mul_of_nonneg_left (hRotBox_mass.trans hmeas_le) (pow_nonneg hT_pos.le _)

#print axioms prodLocalMatrix_mem_unitary
#print axioms gaussian_hiddenRotatedIsing_claw_tube_tail

end
end GaloisForLFunctions.HTGeometry.AccuracyScales.TenthPlateau
