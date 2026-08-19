import GaloisForLFunctions.HTGeometry.PositiveMapTraceNormContraction
import GaloisForLFunctions.HTGeometry.ReturnRecoveryReflection

/-!
# Quantum channels and the diamond distance

A finite-dimensional quantum channel is a linear, completely positive, trace-preserving map of
matrices.  Channels compose, and the diamond distance

`d_◇(Φ, Ψ) = sup { ‖(Φ ⊗ id)(ρ) − (Ψ ⊗ id)(ρ)‖₁ : ρ an ancilla-assisted state }`

makes the monoid of channels a metric space in which left composition contracts and right
composition by a unitary channel is an isometry.  These are exactly the two hypotheses of the
abstract reflection law in `ReturnRecoveryReflection`.
-/

open Matrix
open scoped Matrix ComplexOrder MatrixOrder BigOperators Kronecker

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **A finite-dimensional quantum channel**: linear, completely positive, trace preserving. -/
structure QuantumChannel (n : Type*) [Fintype n] [DecidableEq n] where
  /-- The underlying map of matrices. -/
  map : Matrix n n ℂ → Matrix n n ℂ
  /-- Additivity. -/
  map_add : ∀ X Y, map (X + Y) = map X + map Y
  /-- Complex homogeneity. -/
  map_smul : ∀ (c : ℂ) (X), map (c • X) = c • map X
  /-- Complete positivity: every ancilla amplification is positive. -/
  completelyPositive : ∀ (m : Type) [Fintype m] [DecidableEq m]
      (X : Matrix (n × m) (n × m) ℂ), X.PosSemidef → (amplify map m X).PosSemidef
  /-- Trace preservation. -/
  tracePreserving : ∀ X, (map X).trace = X.trace

namespace QuantumChannel

@[ext] theorem ext {c d : QuantumChannel n} (h : c.map = d.map) : c = d := by
  cases c; cases d; simp_all

omit [Fintype n] [DecidableEq n] in
/-- The one-dimensional ancilla identification. -/
theorem posSemidef_blockMat_fin_one (X : Matrix n n ℂ) :
    (blockMat (fun _ _ : Fin 1 => X)).PosSemidef ↔ X.PosSemidef := by
  have he : blockMat (fun _ _ : Fin 1 => X)
      = X.submatrix (Equiv.prodUnique n (Fin 1)) (Equiv.prodUnique n (Fin 1)) := rfl
  rw [he]
  exact Matrix.posSemidef_submatrix_equiv _

/-- **A channel is positive.** -/
theorem positive (c : QuantumChannel n) {X : Matrix n n ℂ} (hX : X.PosSemidef) :
    (c.map X).PosSemidef := by
  have h1 : (blockMat (fun _ _ : Fin 1 => X)).PosSemidef :=
    (posSemidef_blockMat_fin_one X).mpr hX
  have h2 := c.completelyPositive (Fin 1) _ h1
  rw [amplify_blockMat] at h2
  exact (posSemidef_blockMat_fin_one (c.map X)).mp h2

/-- A channel is a positive trace-preserving map. -/
theorem isPositiveTP (c : QuantumChannel n) : IsPositiveTP c.map where
  map_add := c.map_add
  map_smul := c.map_smul
  pos := fun _ hX => c.positive hX
  tp := c.tracePreserving

/-- Every ancilla amplification of a channel is a positive trace-preserving map. -/
theorem isPositiveTP_amplify_anc (c : QuantumChannel n) (m : Type) [Fintype m] [DecidableEq m] :
    IsPositiveTP (amplify c.map m) :=
  isPositiveTP_amplify c.isPositiveTP (c.completelyPositive m)

/-- Every ancilla amplification of a channel is a positive trace-preserving map. -/
theorem isPositiveTP_amplify_fin (c : QuantumChannel n) (k : ℕ) :
    IsPositiveTP (amplify c.map (Fin k)) :=
  c.isPositiveTP_amplify_anc (Fin k)

instance : One (QuantumChannel n) where
  one :=
    { map := id
      map_add := fun _ _ => rfl
      map_smul := fun _ _ => rfl
      completelyPositive := fun _ _ _ _ hX => hX
      tracePreserving := fun _ => rfl }

instance : Mul (QuantumChannel n) where
  mul c d :=
    { map := c.map ∘ d.map
      map_add := fun X Y => by simp [Function.comp, d.map_add, c.map_add]
      map_smul := fun a X => by simp [Function.comp, d.map_smul, c.map_smul]
      completelyPositive := fun m _ _ X hX => by
        have : amplify (c.map ∘ d.map) m X = amplify c.map m (amplify d.map m X) := rfl
        rw [this]
        exact c.completelyPositive m _ (d.completelyPositive m X hX)
      tracePreserving := fun X => by
        show (c.map (d.map X)).trace = X.trace
        rw [c.tracePreserving, d.tracePreserving] }

@[simp] theorem one_map : (1 : QuantumChannel n).map = id := rfl

@[simp] theorem mul_map (c d : QuantumChannel n) : (c * d).map = c.map ∘ d.map := rfl

instance : Monoid (QuantumChannel n) where
  mul_assoc _ _ _ := QuantumChannel.ext rfl
  one_mul _ := QuantumChannel.ext rfl
  mul_one _ := QuantumChannel.ext rfl


/-! ## Density matrices -/

/-- A density matrix: positive semidefinite of unit trace. -/
structure IsDensity {m : Type*} [Fintype m] (X : Matrix m m ℂ) : Prop where
  /-- Positivity. -/
  posSemidef : X.PosSemidef
  /-- Normalisation. -/
  trace_eq_one : X.trace = 1

theorem IsDensity.nuclearNorm {m : Type*} [Fintype m] [DecidableEq m] {X : Matrix m m ℂ}
    (hX : IsDensity X) : finiteMatrixNuclearNorm X = 1 := by
  rw [finiteMatrixNuclearNorm_posSemidef hX.posSemidef, hX.trace_eq_one]
  simp

/-! ## Elementary nuclear-norm consequences -/

theorem trace_im_eq_zero_of_isHermitian {m : Type*} [Fintype m] {A : Matrix m m ℂ}
    (hA : A.IsHermitian) : A.trace.im = 0 := by
  have h : (starRingEnd ℂ) A.trace = A.trace := by
    have := congrArg Matrix.trace hA.eq
    rwa [Matrix.trace_conjTranspose] at this
  exact Complex.conj_eq_iff_im.mp h

theorem trace_eq_ofReal_nuclearNorm {m : Type*} [Fintype m] [DecidableEq m]
    {P : Matrix m m ℂ} (hP : P.PosSemidef) :
    P.trace = ((finiteMatrixNuclearNorm P : ℝ) : ℂ) := by
  rw [finiteMatrixNuclearNorm_posSemidef hP]
  exact Complex.ext rfl (by
    rw [Complex.ofReal_im]
    exact trace_im_eq_zero_of_isHermitian hP.isHermitian)

/-! ## Agreement on states determines a positive map -/

omit [Fintype n] [DecidableEq n] in
theorem exists_hermitian_decomposition (X : Matrix n n ℂ) :
    ∃ A B : Matrix n n ℂ, A.IsHermitian ∧ B.IsHermitian ∧ X = A + Complex.I • B := by
  refine ⟨(2⁻¹ : ℂ) • (X + Xᴴ), ((2⁻¹ : ℂ) * (-Complex.I)) • (X - Xᴴ), ?_, ?_, ?_⟩
  · show ((2⁻¹ : ℂ) • (X + Xᴴ))ᴴ = (2⁻¹ : ℂ) • (X + Xᴴ)
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
      Matrix.conjTranspose_conjTranspose, add_comm]
    norm_num
  · show (((2⁻¹ : ℂ) * (-Complex.I)) • (X - Xᴴ))ᴴ = ((2⁻¹ : ℂ) * (-Complex.I)) • (X - Xᴴ)
    have hstarc : star ((2⁻¹ : ℂ) * (-Complex.I)) = -((2⁻¹ : ℂ) * (-Complex.I)) := by simp
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_conjTranspose, hstarc, show Xᴴ - X = -(X - Xᴴ) by abel,
      smul_neg, neg_smul, neg_neg]
  · have hI : Complex.I * ((2⁻¹ : ℂ) * (-Complex.I)) = (2⁻¹ : ℂ) := by
      have hII : Complex.I * -Complex.I = 1 := by rw [mul_neg, Complex.I_mul_I]; ring
      calc Complex.I * ((2⁻¹ : ℂ) * (-Complex.I))
          = (2⁻¹ : ℂ) * (Complex.I * -Complex.I) := by ring
        _ = (2⁻¹ : ℂ) := by rw [hII, mul_one]
    rw [smul_smul, hI, ← smul_add, show X + Xᴴ + (X - Xᴴ) = (2 : ℂ) • X by
      rw [two_smul]; abel, smul_smul]
    norm_num

/-- **A positive trace-preserving map is determined by its action on states.** -/
theorem IsPositiveTP.eq_of_eqOn_density {Φ Ψ : Matrix n n ℂ → Matrix n n ℂ}
    (hΦ : IsPositiveTP Φ) (hΨ : IsPositiveTP Ψ)
    (h : ∀ ρ : Matrix n n ℂ, IsDensity ρ → Φ ρ = Ψ ρ) : Φ = Ψ := by
  have hpsd : ∀ P : Matrix n n ℂ, P.PosSemidef → Φ P = Ψ P := by
    intro P hP
    by_cases hz : P = 0
    · subst hz; rw [hΦ.map_zero, hΨ.map_zero]
    · have hne : finiteMatrixNuclearNorm P ≠ 0 := by
        intro hcon
        exact hz ((finiteMatrixNuclearNorm_eq_zero_iff P).mp hcon)
      have hnn : (0 : ℝ) ≤ finiteMatrixNuclearNorm P := finiteMatrixNuclearNorm_nonneg P
      have hpos : (0 : ℝ) < finiteMatrixNuclearNorm P := lt_of_le_of_ne hnn (Ne.symm hne)
      have hcne : ((finiteMatrixNuclearNorm P : ℝ) : ℂ) ≠ 0 := by
        simpa using hne
      have hρ : IsDensity (((finiteMatrixNuclearNorm P : ℝ) : ℂ)⁻¹ • P) := by
        constructor
        · refine hP.smul (a := ((finiteMatrixNuclearNorm P : ℝ) : ℂ)⁻¹) ?_
          rw [show ((finiteMatrixNuclearNorm P : ℝ) : ℂ)⁻¹
              = (((finiteMatrixNuclearNorm P)⁻¹ : ℝ) : ℂ) by simp]
          exact Complex.zero_le_real.mpr (le_of_lt (inv_pos.mpr hpos))
        · rw [Matrix.trace_smul, trace_eq_ofReal_nuclearNorm hP, smul_eq_mul,
            inv_mul_cancel₀ hcne]
      have hkey := h _ hρ
      rw [hΦ.map_smul, hΨ.map_smul] at hkey
      exact smul_right_injective (Matrix n n ℂ) (inv_ne_zero hcne) hkey
  have hherm : ∀ A : Matrix n n ℂ, A.IsHermitian → Φ A = Ψ A := by
    intro A hA
    rw [← hermPos_sub_hermNeg hA, hΦ.map_sub, hΨ.map_sub,
      hpsd _ (hermPos_posSemidef A), hpsd _ (hermNeg_posSemidef A)]
  funext X
  obtain ⟨A, B, hA, hB, hX⟩ := exists_hermitian_decomposition X
  rw [hX, hΦ.map_add, hΨ.map_add, hΦ.map_smul, hΨ.map_smul, hherm A hA, hherm B hB]


/-! ## Iterated amplification -/

omit [Fintype n] [DecidableEq n] in
/-- Amplifying twice is amplifying once by the product ancilla, read through the associativity
equivalence. -/
theorem amplify_amplify (Φ : Matrix n n ℂ → Matrix n n ℂ) (m m' : Type)
    [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m']
    (X : Matrix ((n × m) × m') ((n × m) × m') ℂ) :
    amplify (amplify Φ m) m' X
      = (amplify Φ (m × m')
          (X.submatrix (Equiv.prodAssoc n m m').symm (Equiv.prodAssoc n m m').symm)).submatrix
          (Equiv.prodAssoc n m m') (Equiv.prodAssoc n m m') := rfl

/-- **Every amplification of a channel is again two-positive.** -/
theorem twoPositive_amplify (c : QuantumChannel n) (m : Type) [Fintype m] [DecidableEq m]
    (X : Matrix ((n × m) × Fin 2) ((n × m) × Fin 2) ℂ) (hX : X.PosSemidef) :
    (amplify (amplify c.map m) (Fin 2) X).PosSemidef := by
  rw [amplify_amplify]
  refine (Matrix.posSemidef_submatrix_equiv _).mpr ?_
  exact c.completelyPositive (m × Fin 2) _ ((Matrix.posSemidef_submatrix_equiv _).mpr hX)

/-- **A channel contracts the trace norm of every matrix at every ancilla level.** -/
theorem nuclearNorm_amplify_le (c : QuantumChannel n) (m : Type) [Fintype m] [DecidableEq m]
    (X : Matrix (n × m) (n × m) ℂ) :
    finiteMatrixNuclearNorm (amplify c.map m X) ≤ finiteMatrixNuclearNorm X :=
  nuclearNorm_apply_le_of_twoPositive (c.isPositiveTP_amplify_anc m)
    (c.twoPositive_amplify m) X

/-! ## The diamond distance -/

/-- The set of ancilla-assisted trace-norm output distances of two channels, over the unit ball of
the trace norm.  This is the diamond norm of the difference. -/
def diamondDistSet (c d : QuantumChannel n) : Set ℝ :=
  {r | ∃ (k : ℕ) (X : Matrix (n × Fin k) (n × Fin k) ℂ), finiteMatrixNuclearNorm X ≤ 1 ∧
      r = finiteMatrixNuclearNorm (amplify c.map (Fin k) X - amplify d.map (Fin k) X)}

theorem amplify_isDensity (c : QuantumChannel n) {k : ℕ}
    {X : Matrix (n × Fin k) (n × Fin k) ℂ} (hX : IsDensity X) :
    IsDensity (amplify c.map (Fin k) X) :=
  ⟨c.completelyPositive (Fin k) X hX.posSemidef,
    by rw [trace_amplify c.tracePreserving, hX.trace_eq_one]⟩

theorem amplify_zero (c : QuantumChannel n) (m : Type) [Fintype m] [DecidableEq m] :
    amplify c.map m (0 : Matrix (n × m) (n × m) ℂ) = 0 := by
  ext p q
  show c.map (fun i j => (0 : Matrix (n × m) (n × m) ℂ) (i, p.2) (j, q.2)) p.1 q.1 = 0
  rw [show (fun i j => (0 : Matrix (n × m) (n × m) ℂ) (i, p.2) (j, q.2))
      = (0 : Matrix n n ℂ) from rfl, c.isPositiveTP.map_zero]
  rfl

theorem diamondDistSet_bddAbove (c d : QuantumChannel n) : BddAbove (diamondDistSet c d) := by
  refine ⟨2, ?_⟩
  rintro r ⟨k, X, hX, rfl⟩
  have hc := c.nuclearNorm_amplify_le (Fin k) X
  have hd := d.nuclearNorm_amplify_le (Fin k) X
  have := finiteMatrixNuclearNorm_sub_le' (amplify c.map (Fin k) X) (amplify d.map (Fin k) X)
  linarith

theorem diamondDistSet_nonempty (c d : QuantumChannel n) : (diamondDistSet c d).Nonempty := by
  refine ⟨_, ⟨1, 0, ?_, rfl⟩⟩
  rw [finiteMatrixNuclearNorm_zero]
  norm_num

omit [DecidableEq n] in
theorem isDensity_blockMat_fin_one {ρ : Matrix n n ℂ} (hρ : IsDensity ρ) :
    IsDensity (blockMat (fun _ _ : Fin 1 => ρ)) := by
  constructor
  · exact (posSemidef_blockMat_fin_one ρ).mpr hρ.posSemidef
  · rw [blockMat_trace, Finset.sum_const, Finset.card_univ]
    simp [hρ.trace_eq_one]

/-- **The diamond distance** of two channels. -/
def diamondDist (c d : QuantumChannel n) : ℝ := sSup (diamondDistSet c d)

theorem le_diamondDist (c d : QuantumChannel n) {k : ℕ}
    {X : Matrix (n × Fin k) (n × Fin k) ℂ} (hX : finiteMatrixNuclearNorm X ≤ 1) :
    finiteMatrixNuclearNorm (amplify c.map (Fin k) X - amplify d.map (Fin k) X)
      ≤ diamondDist c d :=
  le_csSup (diamondDistSet_bddAbove c d) ⟨k, X, hX, rfl⟩

theorem diamondDist_le {c d : QuantumChannel n} {r : ℝ}
    (h : ∀ (k : ℕ) (X : Matrix (n × Fin k) (n × Fin k) ℂ), finiteMatrixNuclearNorm X ≤ 1 →
      finiteMatrixNuclearNorm (amplify c.map (Fin k) X - amplify d.map (Fin k) X) ≤ r) :
    diamondDist c d ≤ r := by
  refine csSup_le (diamondDistSet_nonempty c d) ?_
  rintro r' ⟨k, X, hX, rfl⟩
  exact h k X hX

theorem diamondDist_nonneg (c d : QuantumChannel n) : 0 ≤ diamondDist c d := by
  have h := le_diamondDist c d (k := 1) (X := 0) (by rw [finiteMatrixNuclearNorm_zero]; norm_num)
  rw [c.amplify_zero, d.amplify_zero, sub_zero, finiteMatrixNuclearNorm_zero] at h
  exact h

/-- **The diamond distance is the operator norm of the difference on the trace-norm ball.** -/
theorem nuclearNorm_sub_le_diamondDist_mul (c d : QuantumChannel n) (k : ℕ)
    (X : Matrix (n × Fin k) (n × Fin k) ℂ) :
    finiteMatrixNuclearNorm (amplify c.map (Fin k) X - amplify d.map (Fin k) X)
      ≤ diamondDist c d * finiteMatrixNuclearNorm X := by
  by_cases hz : X = 0
  · subst hz
    rw [c.amplify_zero, d.amplify_zero, sub_zero, finiteMatrixNuclearNorm_zero]
    simp
  · have hne : finiteMatrixNuclearNorm X ≠ 0 := fun hcon =>
      hz ((finiteMatrixNuclearNorm_eq_zero_iff X).mp hcon)
    have hpos : 0 < finiteMatrixNuclearNorm X :=
      lt_of_le_of_ne (finiteMatrixNuclearNorm_nonneg X) (Ne.symm hne)
    set t : ℝ := finiteMatrixNuclearNorm X with ht
    have hball : finiteMatrixNuclearNorm (((t⁻¹ : ℝ) : ℂ) • X) ≤ 1 := by
      rw [finiteMatrixNuclearNorm_smul_ofReal _ (le_of_lt (inv_pos.mpr hpos)), ← ht,
        inv_mul_cancel₀ hne]
    have hle := le_diamondDist c d hball
    have hsmul : amplify c.map (Fin k) (((t⁻¹ : ℝ) : ℂ) • X)
        - amplify d.map (Fin k) (((t⁻¹ : ℝ) : ℂ) • X)
        = ((t⁻¹ : ℝ) : ℂ) • (amplify c.map (Fin k) X - amplify d.map (Fin k) X) := by
      rw [(c.isPositiveTP_amplify_fin k).map_smul, (d.isPositiveTP_amplify_fin k).map_smul,
        smul_sub]
    rw [hsmul, finiteMatrixNuclearNorm_smul_ofReal _ (le_of_lt (inv_pos.mpr hpos))] at hle
    have hfin := mul_le_mul_of_nonneg_right hle (le_of_lt hpos)
    calc finiteMatrixNuclearNorm (amplify c.map (Fin k) X - amplify d.map (Fin k) X)
        = t⁻¹ * finiteMatrixNuclearNorm
            (amplify c.map (Fin k) X - amplify d.map (Fin k) X) * t := by
          field_simp
      _ ≤ diamondDist c d * t := hfin

instance : MetricSpace (QuantumChannel n) where
  dist := fun c d => diamondDist c d
  dist_self := by
    intro c
    have hset : diamondDistSet c c = {0} := by
      ext r
      constructor
      · rintro ⟨k, X, hX, rfl⟩
        simp [finiteMatrixNuclearNorm_zero]
      · rintro rfl
        exact ⟨1, 0, by rw [finiteMatrixNuclearNorm_zero]; norm_num,
          by simp [finiteMatrixNuclearNorm_zero]⟩
    show diamondDist c c = 0
    rw [diamondDist, hset, csSup_singleton]
  dist_comm := by
    intro c d
    have hset : diamondDistSet c d = diamondDistSet d c := by
      ext r
      constructor <;> rintro ⟨k, X, hX, rfl⟩ <;>
        exact ⟨k, X, hX, by rw [← finiteMatrixNuclearNorm_neg, neg_sub]⟩
    show diamondDist c d = diamondDist d c
    rw [diamondDist, diamondDist, hset]
  dist_triangle := by
    intro c e d
    show diamondDist c d ≤ diamondDist c e + diamondDist e d
    refine diamondDist_le ?_
    intro k X hX
    have hsplit : amplify c.map (Fin k) X - amplify d.map (Fin k) X
        = (amplify c.map (Fin k) X - amplify e.map (Fin k) X)
          + (amplify e.map (Fin k) X - amplify d.map (Fin k) X) := by abel
    rw [hsplit]
    refine le_trans (finiteMatrixNuclearNorm_add_le' _ _) ?_
    exact add_le_add (le_diamondDist c e hX) (le_diamondDist e d hX)
  eq_of_dist_eq_zero := by
    intro c d hcd
    have hzero : diamondDist c d = 0 := hcd
    refine QuantumChannel.ext ?_
    refine IsPositiveTP.eq_of_eqOn_density c.isPositiveTP d.isPositiveTP ?_
    intro ρ hρ
    have hlift := isDensity_blockMat_fin_one hρ
    have hball : finiteMatrixNuclearNorm (blockMat (fun _ _ : Fin 1 => ρ)) ≤ 1 :=
      le_of_eq hlift.nuclearNorm
    have hle := le_diamondDist c d hball
    rw [hzero] at hle
    have hnn := finiteMatrixNuclearNorm_nonneg
      (amplify c.map (Fin 1) (blockMat (fun _ _ : Fin 1 => ρ))
        - amplify d.map (Fin 1) (blockMat (fun _ _ : Fin 1 => ρ)))
    have hmat := (finiteMatrixNuclearNorm_eq_zero_iff _).mp (le_antisymm hle hnn)
    rw [amplify_blockMat, amplify_blockMat] at hmat
    funext i j
    have hentry := congrFun (congrFun hmat (i, 0)) (j, 0)
    simpa [blockMat, Matrix.sub_apply, sub_eq_zero] using hentry

theorem dist_eq_diamondDist (c d : QuantumChannel n) : dist c d = diamondDist c d := rfl

/-- **Left composition contracts the diamond distance.**  This is the `LeftContracting`
hypothesis of the abstract reflection law, verified for quantum channels. -/
theorem leftContracting_quantumChannel :
    LeftContracting (QuantumChannel n) := by
  intro a b e
  show diamondDist (e * a) (e * b) ≤ diamondDist a b
  refine diamondDist_le ?_
  intro k X hX
  have hamp : IsPositiveTP (amplify e.map (Fin k)) := e.isPositiveTP_amplify_fin k
  have hrw : amplify (e * a).map (Fin k) X - amplify (e * b).map (Fin k) X
      = amplify e.map (Fin k)
          (amplify a.map (Fin k) X - amplify b.map (Fin k) X) := by
    rw [hamp.map_sub]
    rfl
  rw [hrw]
  exact le_trans (e.nuclearNorm_amplify_le (Fin k) _) (le_diamondDist a b hX)

/-! ## Unitary channels -/

theorem star_mem_unitary {U : Matrix n n ℂ} (hU : U ∈ unitary (Matrix n n ℂ)) :
    star U ∈ unitary (Matrix n n ℂ) := by
  refine ⟨?_, ?_⟩
  · show star (star U) * star U = 1
    rw [star_star]; exact hU.2
  · show star U * star (star U) = 1
    rw [star_star]; exact hU.1

/-- The channel of conjugation by a unitary matrix. -/
def unitaryChannel {U : Matrix n n ℂ} (hU : U ∈ unitary (Matrix n n ℂ)) :
    QuantumChannel n where
  map := fun X => U * X * star U
  map_add := fun X Y => by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul := fun a X => by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  completelyPositive := fun m _ _ X hX => by
    rw [amplify_conj]
    have := hX.mul_mul_conjTranspose_same ((U ⊗ₖ (1 : Matrix m m ℂ)))
    simpa [Matrix.star_eq_conjTranspose] using this
  tracePreserving := fun X => by
    rw [Matrix.trace_mul_cycle, hU.1, Matrix.one_mul]

@[simp] theorem unitaryChannel_map {U : Matrix n n ℂ} (hU : U ∈ unitary (Matrix n n ℂ))
    (X : Matrix n n ℂ) : (unitaryChannel hU).map X = U * X * star U := rfl

theorem unitaryChannel_comp_star {U : Matrix n n ℂ} (hU : U ∈ unitary (Matrix n n ℂ))
    (X : Matrix n n ℂ) :
    (unitaryChannel hU).map ((unitaryChannel (star_mem_unitary hU)).map X) = X := by
  show U * (star U * X * star (star U)) * star U = X
  rw [star_star]
  calc U * (star U * X * U) * star U = (U * star U) * X * (U * star U) := by
        simp [Matrix.mul_assoc]
    _ = X := by rw [hU.2, Matrix.one_mul, Matrix.mul_one]

theorem star_unitaryChannel_comp {U : Matrix n n ℂ} (hU : U ∈ unitary (Matrix n n ℂ))
    (X : Matrix n n ℂ) :
    (unitaryChannel (star_mem_unitary hU)).map ((unitaryChannel hU).map X) = X := by
  show star U * (U * X * star U) * star (star U) = X
  rw [star_star]
  calc star U * (U * X * star U) * U = (star U * U) * X * (star U * U) := by
        simp [Matrix.mul_assoc]
    _ = X := by rw [hU.1, Matrix.one_mul, Matrix.mul_one]

theorem unitaryChannel_mul_star {U : Matrix n n ℂ} (hU : U ∈ unitary (Matrix n n ℂ)) :
    unitaryChannel hU * unitaryChannel (star_mem_unitary hU) = 1 :=
  QuantumChannel.ext (funext fun X => unitaryChannel_comp_star hU X)

theorem star_unitaryChannel_mul {U : Matrix n n ℂ} (hU : U ∈ unitary (Matrix n n ℂ)) :
    unitaryChannel (star_mem_unitary hU) * unitaryChannel hU = 1 :=
  QuantumChannel.ext (funext fun X => star_unitaryChannel_comp hU X)

theorem amplify_mul (c d : QuantumChannel n) (k : ℕ)
    (Z : Matrix (n × Fin k) (n × Fin k) ℂ) :
    amplify (c * d).map (Fin k) Z = amplify c.map (Fin k) (amplify d.map (Fin k) Z) := rfl

theorem amplify_unitaryChannel_comp_star {U : Matrix n n ℂ} (hU : U ∈ unitary (Matrix n n ℂ))
    (k : ℕ) (Y : Matrix (n × Fin k) (n × Fin k) ℂ) :
    amplify (unitaryChannel hU).map (Fin k)
        (amplify (unitaryChannel (star_mem_unitary hU)).map (Fin k) Y) = Y := by
  ext p q
  show (unitaryChannel hU).map
      ((unitaryChannel (star_mem_unitary hU)).map (matBlock Y p.2 q.2)) p.1 q.1 = Y p q
  rw [unitaryChannel_comp_star hU]
  rfl

/-- **Right composition by a unitary channel is a diamond isometry.**  This is the second
hypothesis of the abstract reflection law, verified for quantum channels. -/
theorem diamondDist_mul_unitaryChannel (c d : QuantumChannel n) {U : Matrix n n ℂ}
    (hU : U ∈ unitary (Matrix n n ℂ)) :
    diamondDist (c * unitaryChannel hU) (d * unitaryChannel hU) = diamondDist c d := by
  refine le_antisymm (diamondDist_le ?_) (diamondDist_le ?_)
  · intro k X hX
    rw [amplify_mul, amplify_mul]
    exact le_diamondDist c d
      (le_trans ((unitaryChannel hU).nuclearNorm_amplify_le (Fin k) X) hX)
  · intro k Y hY
    have hYd : finiteMatrixNuclearNorm
        (amplify (unitaryChannel (star_mem_unitary hU)).map (Fin k) Y) ≤ 1 :=
      le_trans ((unitaryChannel (star_mem_unitary hU)).nuclearNorm_amplify_le (Fin k) Y) hY
    have hle := le_diamondDist (c * unitaryChannel hU) (d * unitaryChannel hU) hYd
    rw [amplify_mul, amplify_mul, amplify_unitaryChannel_comp_star hU] at hle
    exact hle


end QuantumChannel

end

end GaloisForLFunctions.HTGeometry
