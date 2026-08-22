import Mathlib

/-!
# DQPT: the probe reduced density matrix

Methods equations (20)–(21) of arXiv:2511.11199.  A probe qubit prepared in `|↑⟩` is coupled to
a system in the diagonal thermal state `ρ_s = diag p` through
`H_c = ½ σ_x ⊗ (H₀ − θ̇ I)`, so that after time `t` the joint unitary is
`U = exp(−(i/2) σ_x ⊗ A)` with `A(t) = H₀t − θ(t)` diagonal.  Then

* **(20)**  `U ρ₀ U† = ½[|+⟩⟨+|⊗ρ_s + e^{−iA}|+⟩⟨−|⊗ρ_s + e^{iA}|−⟩⟨+|⊗ρ_s + |−⟩⟨−|⊗ρ_s]`;
* **(21)**  `ρ_probe = ½I + ½ Re S(t) σ_z + ½ Im S(t) σ_y`,  `S(t) = Tr(e^{−iA}ρ_s)`.

Everything is block diagonal in the system index, so the whole computation reduces to a `2 × 2`
identity per level, obtained by diagonalising `σ_x` with the Hadamard matrix.

Main results:
* `dqpt_exp_sigmaX` — `exp(−(i a/2) σ_x) = cos(a/2)·1 − i sin(a/2)·σ_x`;
* `dqpt_evolved_level` — **(20)** at a single level;
* `dqptEvolution_eq_exp` — the joint evolution is the claimed exponential;
* `dqpt_evolved_state` — **(20)**;
* `dqpt_probe_density` — **(21)**.
-/

namespace RHTower.DQPT

open Filter Topology Set

noncomputable section

/-! ## The one-qubit algebra -/

def dqptSigmaX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def dqptSigmaY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
def dqptSigmaZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
def dqptHad : Matrix (Fin 2) (Fin 2) ℂ := (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ • !![1, 1; 1, -1]

/-- `|↑⟩⟨↑|`. -/
def dqptUp : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]

/-- `|+⟩⟨+|`. -/
def dqptPP : Matrix (Fin 2) (Fin 2) ℂ := (2 : ℂ)⁻¹ • !![1, 1; 1, 1]
/-- `|+⟩⟨−|`. -/
def dqptPM : Matrix (Fin 2) (Fin 2) ℂ := (2 : ℂ)⁻¹ • !![1, -1; 1, -1]
/-- `|−⟩⟨+|`. -/
def dqptMP : Matrix (Fin 2) (Fin 2) ℂ := (2 : ℂ)⁻¹ • !![1, 1; -1, -1]
/-- `|−⟩⟨−|`. -/
def dqptMM : Matrix (Fin 2) (Fin 2) ℂ := (2 : ℂ)⁻¹ • !![1, -1; -1, 1]

/-- The single-level evolution `exp(−(i a/2) σ_x)`. -/
def dqptUblk (a : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((Real.cos (a / 2) : ℝ) : ℂ), -Complex.I * ((Real.sin (a / 2) : ℝ) : ℂ);
     -Complex.I * ((Real.sin (a / 2) : ℝ) : ℂ), ((Real.cos (a / 2) : ℝ) : ℂ)]

theorem dqpt_sqrt_two_sq : (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ * (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ = (2 : ℂ)⁻¹ := by
  have h : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = (2 : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  field_simp
  rw [← h]
  ring

theorem dqptHad_mul_self : dqptHad * dqptHad = 1 := by
  rw [dqptHad, Matrix.smul_mul, Matrix.mul_smul, smul_smul, dqpt_sqrt_two_sq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

theorem dqptHad_conj_sigmaZ : dqptHad * dqptSigmaZ * dqptHad = dqptSigmaX := by
  rw [dqptHad, dqptSigmaZ, dqptSigmaX, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
    smul_smul, dqpt_sqrt_two_sq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-- `exp(−(i a/2) σ_x) = cos(a/2)·1 − i sin(a/2)·σ_x`. -/
theorem dqpt_exp_sigmaX (a : ℝ) :
    NormedSpace.exp ((-(Complex.I * ((a : ℝ) : ℂ) / 2)) • dqptSigmaX) = dqptUblk a := by
  set c : ℂ := -(Complex.I * ((a : ℝ) : ℂ) / 2) with hc
  set U : (Matrix (Fin 2) (Fin 2) ℂ)ˣ :=
    ⟨dqptHad, dqptHad, dqptHad_mul_self, dqptHad_mul_self⟩ with hUdef
  have hU : (U : Matrix (Fin 2) (Fin 2) ℂ) = dqptHad := rfl
  have hUi : ((U⁻¹ : (Matrix (Fin 2) (Fin 2) ℂ)ˣ) : Matrix (Fin 2) (Fin 2) ℂ) = dqptHad := rfl
  have hconj : c • dqptSigmaX
      = (U : Matrix (Fin 2) (Fin 2) ℂ) * (c • dqptSigmaZ)
        * ((U⁻¹ : (Matrix (Fin 2) (Fin 2) ℂ)ˣ) : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [hU, hUi, Matrix.mul_smul, Matrix.smul_mul, dqptHad_conj_sigmaZ]
  have hdiag : c • dqptSigmaZ = Matrix.diagonal ![c, -c] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [dqptSigmaZ, Matrix.diagonal]
  have hexpdiag : NormedSpace.exp (c • dqptSigmaZ)
      = Matrix.diagonal ![NormedSpace.exp c, NormedSpace.exp (-c)] := by
    rw [hdiag, Matrix.exp_diagonal]
    congr 1
    funext i
    rw [Pi.coe_exp]
    fin_cases i <;> rfl
  rw [hconj, Matrix.exp_units_conj, hexpdiag, hU, hUi]
  have hexpc : NormedSpace.exp c = ((Real.cos (a / 2) : ℝ) : ℂ)
      - Complex.I * ((Real.sin (a / 2) : ℝ) : ℂ) := by
    rw [hc, ← Complex.exp_eq_exp_ℂ]
    have harg : -(Complex.I * ((a : ℝ) : ℂ) / 2) = ((-(a / 2) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [harg, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg,
      Real.sin_neg]
    push_cast
    ring
  have hexpnc : NormedSpace.exp (-c) = ((Real.cos (a / 2) : ℝ) : ℂ)
      + Complex.I * ((Real.sin (a / 2) : ℝ) : ℂ) := by
    rw [hc, ← Complex.exp_eq_exp_ℂ]
    have harg : -(-(Complex.I * ((a : ℝ) : ℂ) / 2)) = (((a / 2) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [harg, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    push_cast
    ring
  have hdiagmat : Matrix.diagonal ![NormedSpace.exp c, NormedSpace.exp (-c)]
      = !![NormedSpace.exp c, 0; 0, NormedSpace.exp (-c)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
  rw [hdiagmat, hexpc, hexpnc, dqptHad, dqptUblk]
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, dqpt_sqrt_two_sq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-- **Methods (20) at one level.** -/
theorem dqpt_evolved_level (a : ℝ) :
    dqptUblk a * dqptUp * (dqptUblk a).conjTranspose
      = (2 : ℂ)⁻¹ • (dqptPP + Complex.exp (-Complex.I * ((a : ℝ) : ℂ)) • dqptPM
          + Complex.exp (Complex.I * ((a : ℝ) : ℂ)) • dqptMP + dqptMM) := by
  have hhalfm : Complex.exp (-Complex.I * (((a / 2) : ℝ) : ℂ))
      = ((Real.cos (a / 2) : ℝ) : ℂ) - Complex.I * ((Real.sin (a / 2) : ℝ) : ℂ) := by
    have harg : -Complex.I * (((a / 2) : ℝ) : ℂ) = ((-(a / 2) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [harg, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg,
      Real.sin_neg]
    push_cast
    ring
  have hhalfp : Complex.exp (Complex.I * (((a / 2) : ℝ) : ℂ))
      = ((Real.cos (a / 2) : ℝ) : ℂ) + Complex.I * ((Real.sin (a / 2) : ℝ) : ℂ) := by
    have harg : Complex.I * (((a / 2) : ℝ) : ℂ) = (((a / 2) : ℝ) : ℂ) * Complex.I := by ring
    rw [harg, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    ring
  have hexpm : Complex.exp (-Complex.I * ((a : ℝ) : ℂ))
      = (((Real.cos (a / 2) : ℝ) : ℂ) - Complex.I * ((Real.sin (a / 2) : ℝ) : ℂ)) ^ 2 := by
    rw [sq, ← hhalfm, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hexpp : Complex.exp (Complex.I * ((a : ℝ) : ℂ))
      = (((Real.cos (a / 2) : ℝ) : ℂ) + Complex.I * ((Real.sin (a / 2) : ℝ) : ℂ)) ^ 2 := by
    rw [sq, ← hhalfp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hconjT : (dqptUblk a).conjTranspose
      = !![((Real.cos (a / 2) : ℝ) : ℂ), Complex.I * ((Real.sin (a / 2) : ℝ) : ℂ);
           Complex.I * ((Real.sin (a / 2) : ℝ) : ℂ), ((Real.cos (a / 2) : ℝ) : ℂ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [dqptUblk, Matrix.conjTranspose_apply, -Complex.ofReal_cos, -Complex.ofReal_sin]
  rw [hexpm, hexpp, hconjT, dqptUblk, dqptUp, dqptPP, dqptPM, dqptMP, dqptMM]
  set c : ℂ := ((Real.cos (a / 2) : ℝ) : ℂ) with hcdef
  set s : ℂ := ((Real.sin (a / 2) : ℝ) : ℂ) with hsdef
  have hpy : s ^ 2 + c ^ 2 = 1 := by
    have h := Real.sin_sq_add_cos_sq (a / 2)
    rw [hcdef, hsdef, ← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add, h]
    norm_num
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  ext i j
  fin_cases i
  · fin_cases j
    · simp
      linear_combination (1 / 2 : ℂ) * hpy - (s ^ 2 / 2) * hI
    · simp
      ring
  · fin_cases j
    · simp
      ring
    · simp
      linear_combination (1 / 2 : ℂ) * hpy - (s ^ 2 / 2) * hI

end

end RHTower.DQPT

namespace RHTower.DQPT

open Filter Topology Set

noncomputable section

/-! ## The joint evolution and the reduced probe state -/

/-- The joint coupling `−(i/2)·σ_x ⊗ A`, block diagonal in the system index. -/
def dqptCoupling {N : ℕ} (A : Fin N → ℝ) : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℂ :=
  Matrix.blockDiagonal (fun n => (-(Complex.I * ((A n : ℝ) : ℂ) / 2)) • dqptSigmaX)

/-- The joint evolution operator. -/
def dqptEvolution {N : ℕ} (A : Fin N → ℝ) : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℂ :=
  Matrix.blockDiagonal (fun n => dqptUblk (A n))

/-- The initial joint state `|↑⟩⟨↑| ⊗ ρ_s` with `ρ_s = diag p`. -/
def dqptInitial {N : ℕ} (p : Fin N → ℝ) : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℂ :=
  Matrix.blockDiagonal (fun n => ((p n : ℝ) : ℂ) • dqptUp)

/-- The joint Hadamard, block diagonal in the system index. -/
def dqptHadBig (N : ℕ) : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℂ :=
  Matrix.blockDiagonal (fun _ : Fin N => dqptHad)

theorem dqptHadBig_mul_self (N : ℕ) : dqptHadBig N * dqptHadBig N = 1 := by
  rw [dqptHadBig, ← Matrix.blockDiagonal_mul,
    show (fun _ : Fin N => dqptHad * dqptHad) = fun _ : Fin N => (1 : Matrix (Fin 2) (Fin 2) ℂ)
      from funext fun _ => dqptHad_mul_self]
  exact Matrix.blockDiagonal_one

/-- The single-level exponential in Hadamard-conjugated diagonal form. -/
theorem dqptHad_conj_expDiag (a : ℝ) :
    dqptHad * !![Complex.exp (-(Complex.I * ((a : ℝ) : ℂ) / 2)), 0;
                 0, Complex.exp (Complex.I * ((a : ℝ) : ℂ) / 2)] * dqptHad = dqptUblk a := by
  have hm : Complex.exp (-(Complex.I * ((a : ℝ) : ℂ) / 2))
      = ((Real.cos (a / 2) : ℝ) : ℂ) - Complex.I * ((Real.sin (a / 2) : ℝ) : ℂ) := by
    have harg : -(Complex.I * ((a : ℝ) : ℂ) / 2) = ((-(a / 2) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [harg, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg,
      Real.sin_neg]
    push_cast
    ring
  have hp : Complex.exp (Complex.I * ((a : ℝ) : ℂ) / 2)
      = ((Real.cos (a / 2) : ℝ) : ℂ) + Complex.I * ((Real.sin (a / 2) : ℝ) : ℂ) := by
    have harg : Complex.I * ((a : ℝ) : ℂ) / 2 = (((a / 2) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [harg, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    ring
  rw [hm, hp, dqptHad, dqptUblk, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
    dqpt_sqrt_two_sq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [-Complex.ofReal_cos, -Complex.ofReal_sin] <;> ring

/-- The `σ_z` block form of the coupling is diagonal. -/
theorem dqptBlockZ_eq_diagonal {N : ℕ} (A : Fin N → ℝ) :
    Matrix.blockDiagonal (fun n => (-(Complex.I * ((A n : ℝ) : ℂ) / 2)) • dqptSigmaZ)
      = Matrix.diagonal (fun q : Fin 2 × Fin N =>
          if q.1 = 0 then -(Complex.I * ((A q.2 : ℝ) : ℂ) / 2)
          else Complex.I * ((A q.2 : ℝ) : ℂ) / 2) := by
  ext q r
  obtain ⟨i, m⟩ := q
  obtain ⟨j, n⟩ := r
  rw [Matrix.blockDiagonal_apply, Matrix.diagonal_apply]
  by_cases h : m = n
  · subst h
    fin_cases i <;> fin_cases j <;> simp [dqptSigmaZ, Prod.ext_iff]
  · simp [h, Prod.ext_iff]

/-- The exponentiated diagonal is again block diagonal. -/
theorem dqptExpDiag_eq_blockDiagonal {N : ℕ} (A : Fin N → ℝ) :
    Matrix.diagonal (fun q : Fin 2 × Fin N => Complex.exp
        (if q.1 = 0 then -(Complex.I * ((A q.2 : ℝ) : ℂ) / 2)
          else Complex.I * ((A q.2 : ℝ) : ℂ) / 2))
      = Matrix.blockDiagonal (fun n : Fin N =>
          !![Complex.exp (-(Complex.I * ((A n : ℝ) : ℂ) / 2)), 0;
             0, Complex.exp (Complex.I * ((A n : ℝ) : ℂ) / 2)]) := by
  ext q r
  obtain ⟨i, m⟩ := q
  obtain ⟨j, n⟩ := r
  rw [Matrix.blockDiagonal_apply, Matrix.diagonal_apply]
  by_cases h : m = n
  · subst h
    fin_cases i <;> fin_cases j <;> simp [Prod.ext_iff]
  · simp [h, Prod.ext_iff]

theorem dqptCoupling_conj {N : ℕ} (A : Fin N → ℝ) :
    dqptCoupling A = dqptHadBig N
      * Matrix.blockDiagonal (fun n => (-(Complex.I * ((A n : ℝ) : ℂ) / 2)) • dqptSigmaZ)
      * dqptHadBig N := by
  rw [dqptHadBig, ← Matrix.blockDiagonal_mul, ← Matrix.blockDiagonal_mul, dqptCoupling]
  congr 1
  funext n
  rw [Matrix.mul_smul, Matrix.smul_mul, dqptHad_conj_sigmaZ]

theorem dqptEvolution_eq_exp {N : ℕ} (A : Fin N → ℝ) :
    dqptEvolution A = NormedSpace.exp (dqptCoupling A) := by
  set U : (Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℂ)ˣ :=
    ⟨dqptHadBig N, dqptHadBig N, dqptHadBig_mul_self N, dqptHadBig_mul_self N⟩ with hUdef
  have hU : (U : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℂ) = dqptHadBig N := rfl
  have hUi : ((U⁻¹ : (Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℂ)ˣ) :
      Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℂ) = dqptHadBig N := rfl
  have hconj : dqptCoupling A = (U : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℂ)
      * Matrix.diagonal (fun q : Fin 2 × Fin N =>
          if q.1 = 0 then -(Complex.I * ((A q.2 : ℝ) : ℂ) / 2)
          else Complex.I * ((A q.2 : ℝ) : ℂ) / 2)
      * ((U⁻¹ : (Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℂ)ˣ) :
          Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℂ) := by
    rw [hU, hUi, ← dqptBlockZ_eq_diagonal, ← dqptCoupling_conj]
  rw [hconj, Matrix.exp_units_conj, Matrix.exp_diagonal, hU, hUi]
  have hpi : (NormedSpace.exp (fun q : Fin 2 × Fin N =>
        if q.1 = 0 then -(Complex.I * ((A q.2 : ℝ) : ℂ) / 2)
        else Complex.I * ((A q.2 : ℝ) : ℂ) / 2))
      = fun q : Fin 2 × Fin N => Complex.exp
        (if q.1 = 0 then -(Complex.I * ((A q.2 : ℝ) : ℂ) / 2)
          else Complex.I * ((A q.2 : ℝ) : ℂ) / 2) := by
    funext q
    rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]
  rw [hpi, dqptExpDiag_eq_blockDiagonal, dqptHadBig, ← Matrix.blockDiagonal_mul,
    ← Matrix.blockDiagonal_mul, dqptEvolution]
  congr 1
  funext n
  exact (dqptHad_conj_expDiag (A n)).symm

/-- **Methods (20).** -/
theorem dqpt_evolved_state {N : ℕ} (A : Fin N → ℝ) (p : Fin N → ℝ) :
    dqptEvolution A * dqptInitial p * (dqptEvolution A).conjTranspose
      = Matrix.blockDiagonal (fun n => ((p n : ℝ) : ℂ) •
          ((2 : ℂ)⁻¹ • (dqptPP + Complex.exp (-Complex.I * ((A n : ℝ) : ℂ)) • dqptPM
            + Complex.exp (Complex.I * ((A n : ℝ) : ℂ)) • dqptMP + dqptMM))) := by
  rw [dqptEvolution, dqptInitial, Matrix.blockDiagonal_conjTranspose,
    ← Matrix.blockDiagonal_mul, ← Matrix.blockDiagonal_mul]
  congr 1
  funext n
  rw [Matrix.mul_smul, Matrix.smul_mul, dqpt_evolved_level (A n)]

/-- The partial trace over the system register. -/
def dqptPTrace {N : ℕ} (M : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ := Matrix.of fun i j => ∑ n : Fin N, M (i, n) (j, n)

theorem dqptPTrace_blockDiagonal {N : ℕ} (M : Fin N → Matrix (Fin 2) (Fin 2) ℂ) :
    dqptPTrace (Matrix.blockDiagonal M) = ∑ n : Fin N, M n := by
  ext i j
  rw [dqptPTrace, Matrix.sum_apply]
  simp [Matrix.blockDiagonal_apply]

/-- The Loschmidt readout `S(t) = Tr(e^{−iA}ρ_s)`. -/
def dqptSAmp {N : ℕ} (A p : Fin N → ℝ) : ℂ :=
  ∑ n, ((p n : ℝ) : ℂ) * Complex.exp (-Complex.I * ((A n : ℝ) : ℂ))

theorem dqpt_exp_neg_I_real (a : ℝ) :
    Complex.exp (-Complex.I * ((a : ℝ) : ℂ))
      = ((Real.cos a : ℝ) : ℂ) - Complex.I * ((Real.sin a : ℝ) : ℂ) := by
  have harg : -Complex.I * ((a : ℝ) : ℂ) = ((-a : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [harg, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg,
    Real.sin_neg]
  push_cast
  ring

theorem dqpt_exp_pos_I_real (a : ℝ) :
    Complex.exp (Complex.I * ((a : ℝ) : ℂ))
      = ((Real.cos a : ℝ) : ℂ) + Complex.I * ((Real.sin a : ℝ) : ℂ) := by
  have harg : Complex.I * ((a : ℝ) : ℂ) = ((a : ℝ) : ℂ) * Complex.I := by ring
  rw [harg, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  ring

theorem dqptSAmp_re {N : ℕ} (A p : Fin N → ℝ) :
    (dqptSAmp A p).re = ∑ n, p n * Real.cos (A n) := by
  rw [dqptSAmp, Complex.re_sum]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [dqpt_exp_neg_I_real]
  simp [-Complex.ofReal_cos, -Complex.ofReal_sin]

theorem dqptSAmp_im {N : ℕ} (A p : Fin N → ℝ) :
    (dqptSAmp A p).im = ∑ n, p n * (-(Real.sin (A n))) := by
  rw [dqptSAmp, Complex.im_sum]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [dqpt_exp_neg_I_real]
  simp [-Complex.ofReal_cos, -Complex.ofReal_sin]

/-- The one-level state in explicit `2 × 2` form. -/
theorem dqpt_level_matrix (a : ℝ) :
    (2 : ℂ)⁻¹ • (dqptPP + Complex.exp (-Complex.I * ((a : ℝ) : ℂ)) • dqptPM
        + Complex.exp (Complex.I * ((a : ℝ) : ℂ)) • dqptMP + dqptMM)
      = !![(1 + ((Real.cos a : ℝ) : ℂ)) / 2, Complex.I * ((Real.sin a : ℝ) : ℂ) / 2;
           -(Complex.I * ((Real.sin a : ℝ) : ℂ)) / 2, (1 - ((Real.cos a : ℝ) : ℂ)) / 2] := by
  rw [dqpt_exp_neg_I_real, dqpt_exp_pos_I_real, dqptPP, dqptPM, dqptMP, dqptMM]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [-Complex.ofReal_cos, -Complex.ofReal_sin] <;> ring

theorem dqpt_sum_matrix2 {N : ℕ} (a b c d q : Fin N → ℂ) :
    ∑ n, q n • (!![a n, b n; c n, d n] : Matrix (Fin 2) (Fin 2) ℂ)
      = !![∑ n, q n * a n, ∑ n, q n * b n; ∑ n, q n * c n, ∑ n, q n * d n] := by
  ext i j
  rw [Matrix.sum_apply]
  fin_cases i <;> fin_cases j <;> simp

/-- **Methods (21).**  `ρ_probe = ½I + ½ Re S σ_z + ½ Im S σ_y`. -/
theorem dqpt_probe_density {N : ℕ} (A p : Fin N → ℝ) (hp : ∑ n, p n = 1) :
    dqptPTrace (dqptEvolution A * dqptInitial p * (dqptEvolution A).conjTranspose)
      = (2 : ℂ)⁻¹ • (1 : Matrix (Fin 2) (Fin 2) ℂ)
        + ((((dqptSAmp A p).re : ℝ) : ℂ) / 2) • dqptSigmaZ
        + ((((dqptSAmp A p).im : ℝ) : ℂ) / 2) • dqptSigmaY := by
  have hpC : ∑ n, ((p n : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_sum, hp, Complex.ofReal_one]
  have hcosSum : ∑ n, ((p n : ℝ) : ℂ) * ((Real.cos (A n) : ℝ) : ℂ)
      = (((∑ n, p n * Real.cos (A n) : ℝ)) : ℂ) := by
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl (fun n _ => by push_cast; ring)
  have hsinSum : ∑ n, ((p n : ℝ) : ℂ) * ((Real.sin (A n) : ℝ) : ℂ)
      = -(((∑ n, p n * (-(Real.sin (A n))) : ℝ)) : ℂ) := by
    rw [Complex.ofReal_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun n _ => by push_cast; ring)
  rw [dqpt_evolved_state, dqptPTrace_blockDiagonal]
  have hlevel : ∀ n : Fin N, ((p n : ℝ) : ℂ) •
      ((2 : ℂ)⁻¹ • (dqptPP + Complex.exp (-Complex.I * ((A n : ℝ) : ℂ)) • dqptPM
        + Complex.exp (Complex.I * ((A n : ℝ) : ℂ)) • dqptMP + dqptMM))
      = ((p n : ℝ) : ℂ) •
        (!![(1 + ((Real.cos (A n) : ℝ) : ℂ)) / 2,
             Complex.I * ((Real.sin (A n) : ℝ) : ℂ) / 2;
           -(Complex.I * ((Real.sin (A n) : ℝ) : ℂ)) / 2,
             (1 - ((Real.cos (A n) : ℝ) : ℂ)) / 2] : Matrix (Fin 2) (Fin 2) ℂ) := by
    intro n
    rw [dqpt_level_matrix]
  rw [Finset.sum_congr rfl (fun n _ => hlevel n), dqpt_sum_matrix2, dqptSAmp_re, dqptSAmp_im]
  have e1 : ∑ n, ((p n : ℝ) : ℂ) * ((1 + ((Real.cos (A n) : ℝ) : ℂ)) / 2)
      = (1 + (((∑ n, p n * Real.cos (A n) : ℝ)) : ℂ)) / 2 := by
    have hstep : ∀ n : Fin N, ((p n : ℝ) : ℂ) * ((1 + ((Real.cos (A n) : ℝ) : ℂ)) / 2)
        = (((p n : ℝ) : ℂ) + ((p n : ℝ) : ℂ) * ((Real.cos (A n) : ℝ) : ℂ)) / 2 :=
      fun n => by ring
    rw [Finset.sum_congr rfl (fun n _ => hstep n), ← Finset.sum_div, Finset.sum_add_distrib,
      hpC, hcosSum]
  have e2 : ∑ n, ((p n : ℝ) : ℂ) * (Complex.I * ((Real.sin (A n) : ℝ) : ℂ) / 2)
      = -(Complex.I * (((∑ n, p n * (-(Real.sin (A n))) : ℝ)) : ℂ)) / 2 := by
    have hstep : ∀ n : Fin N, ((p n : ℝ) : ℂ) * (Complex.I * ((Real.sin (A n) : ℝ) : ℂ) / 2)
        = Complex.I * (((p n : ℝ) : ℂ) * ((Real.sin (A n) : ℝ) : ℂ)) / 2 := fun n => by ring
    rw [Finset.sum_congr rfl (fun n _ => hstep n), ← Finset.sum_div, ← Finset.mul_sum, hsinSum]
    ring
  have e3 : ∑ n, ((p n : ℝ) : ℂ) * (-(Complex.I * ((Real.sin (A n) : ℝ) : ℂ)) / 2)
      = Complex.I * (((∑ n, p n * (-(Real.sin (A n))) : ℝ)) : ℂ) / 2 := by
    have hstep : ∀ n : Fin N, ((p n : ℝ) : ℂ) * (-(Complex.I * ((Real.sin (A n) : ℝ) : ℂ)) / 2)
        = -(Complex.I * (((p n : ℝ) : ℂ) * ((Real.sin (A n) : ℝ) : ℂ))) / 2 := fun n => by ring
    rw [Finset.sum_congr rfl (fun n _ => hstep n), ← Finset.sum_div, Finset.sum_neg_distrib,
      ← Finset.mul_sum, hsinSum]
    ring
  have e4 : ∑ n, ((p n : ℝ) : ℂ) * ((1 - ((Real.cos (A n) : ℝ) : ℂ)) / 2)
      = (1 - (((∑ n, p n * Real.cos (A n) : ℝ)) : ℂ)) / 2 := by
    have hstep : ∀ n : Fin N, ((p n : ℝ) : ℂ) * ((1 - ((Real.cos (A n) : ℝ) : ℂ)) / 2)
        = (((p n : ℝ) : ℂ) - ((p n : ℝ) : ℂ) * ((Real.cos (A n) : ℝ) : ℂ)) / 2 :=
      fun n => by ring
    rw [Finset.sum_congr rfl (fun n _ => hstep n), ← Finset.sum_div, Finset.sum_sub_distrib,
      hpC, hcosSum]
  rw [e1, e2, e3, e4, dqptSigmaZ, dqptSigmaY]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

end

end RHTower.DQPT
