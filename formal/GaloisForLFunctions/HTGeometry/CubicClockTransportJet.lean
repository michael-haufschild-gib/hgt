import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Clock cubing versus transport differentiation

For clocks `A : E → E`, `B : X → X` and `F : X → E`, left and right multiplication
`L F = A F`, `R F = F B` commute on `Hom(X, E)`.  With `ω₁ = A F - F B` and
`ω₃ = A³ F - F B³`:

* `ω₃ = (L² + L R + R²) ω₁`;
* `J₃ = (L - R)³ F = (L² - 2 L R + R²) ω₁`;
* `ω₃ - J₃ = 3 A ω₁ B`.

The transport orbit `u ↦ exp(uA) F exp(-uB)` has derivative `(L - R)` of itself, so its third
derivative at `0` is `J₃`.  A unipotent clock has `ω₃ ≠ 0 = J₃`, a cube root of unity has
`ω₃ = 0 ≠ J₃`: neither expression determines the other.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section Algebra

variable {E X Q : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [NormedAddCommGroup Q] [NormedSpace ℂ Q]

/-- The transport differential `δ F = A F - F B`. -/
def clockTransport (A : E →L[ℂ] E) (B : X →L[ℂ] X) (F : X →L[ℂ] E) : X →L[ℂ] E :=
  A ∘L F - F ∘L B

/-- The transport differential as a continuous linear map on `Hom(X, E)`. -/
def clockTransportCLM (A : E →L[ℂ] E) (B : X →L[ℂ] X) : (X →L[ℂ] E) →L[ℂ] (X →L[ℂ] E) :=
  ContinuousLinearMap.compL ℂ X E E A - (ContinuousLinearMap.compL ℂ X X E).flip B

@[simp] theorem clockTransportCLM_apply (A : E →L[ℂ] E) (B : X →L[ℂ] X) (F : X →L[ℂ] E) :
    clockTransportCLM A B F = clockTransport A B F := rfl

/-- The powered-clock defect `A³ F - F B³`. -/
def clockCubeDefect (A : E →L[ℂ] E) (B : X →L[ℂ] X) (F : X →L[ℂ] E) : X →L[ℂ] E :=
  (A ^ 3) ∘L F - F ∘L (B ^ 3)

/-- The third transport jet `J₃ = δ³ F`. -/
def clockTransportJet3 (A : E →L[ℂ] E) (B : X →L[ℂ] X) (F : X →L[ℂ] E) : X →L[ℂ] E :=
  clockTransport A B (clockTransport A B (clockTransport A B F))

/-- **(1)** `A³F - FB³ = (L² + LR + R²)(AF - FB)`. -/
theorem clockCubeDefect_eq (A : E →L[ℂ] E) (B : X →L[ℂ] X) (F : X →L[ℂ] E) :
    clockCubeDefect A B F =
      (A ^ 2) ∘L clockTransport A B F + A ∘L clockTransport A B F ∘L B +
        clockTransport A B F ∘L (B ^ 2) := by
  ext x
  simp only [clockCubeDefect, clockTransport, pow_succ, pow_zero, one_mul,
    ContinuousLinearMap.comp_apply, sub_apply, add_apply,
    mul_apply_eq_comp, map_sub]
  abel

/-- **(2)** `J₃ = (L² - 2LR + R²)(AF - FB)`. -/
theorem clockTransportJet3_eq (A : E →L[ℂ] E) (B : X →L[ℂ] X) (F : X →L[ℂ] E) :
    clockTransportJet3 A B F =
      (A ^ 2) ∘L clockTransport A B F - (2 : ℂ) • (A ∘L clockTransport A B F ∘L B) +
        clockTransport A B F ∘L (B ^ 2) := by
  ext x
  simp only [clockTransportJet3, clockTransport, pow_succ, pow_zero, one_mul,
    ContinuousLinearMap.comp_apply, sub_apply, add_apply,
    mul_apply_eq_comp, map_sub, two_smul]
  abel

/-- **(3)** `ω₃ - J₃ = 3 A ω₁ B`. -/
theorem clockCubeDefect_sub_jet3 (A : E →L[ℂ] E) (B : X →L[ℂ] X) (F : X →L[ℂ] E) :
    clockCubeDefect A B F - clockTransportJet3 A B F =
      (3 : ℂ) • (A ∘L clockTransport A B F ∘L B) := by
  rw [clockCubeDefect_eq, clockTransportJet3_eq]
  ext x
  simp only [sub_apply, add_apply,
    smul_apply]
  rw [show (3 : ℂ) = 2 + 1 by norm_num, add_smul, one_smul]
  abel

/-- Quotient naturality: if `q A = A_Q q` then `q J₃(F) = J₃(q F)` for the quotient clock. -/
theorem comp_clockTransportJet3 {A : E →L[ℂ] E} {AQ : Q →L[ℂ] Q} (B : X →L[ℂ] X)
    {q : E →L[ℂ] Q} (hq : q ∘L A = AQ ∘L q) (F : X →L[ℂ] E) :
    q ∘L clockTransportJet3 A B F = clockTransportJet3 AQ B (q ∘L F) := by
  have h1 : ∀ G : X →L[ℂ] E, q ∘L clockTransport A B G = clockTransport AQ B (q ∘L G) := by
    intro G
    simp only [clockTransport, ContinuousLinearMap.comp_sub, ← ContinuousLinearMap.comp_assoc, hq]
  simp only [clockTransportJet3, h1]

/-- The transport third jet lands in `ker q` exactly when the quotient-clock third jet of `q F`
vanishes. -/
theorem clockTransportJet3_mem_ker_iff {A : E →L[ℂ] E} {AQ : Q →L[ℂ] Q} (B : X →L[ℂ] X)
    {q : E →L[ℂ] Q} (hq : q ∘L A = AQ ∘L q) (F : X →L[ℂ] E) :
    q ∘L clockTransportJet3 A B F = 0 ↔ clockTransportJet3 AQ B (q ∘L F) = 0 := by
  rw [comp_clockTransportJet3 B hq F]

end Algebra

/-! ## The transport orbit -/

section Orbit

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- The transport orbit `u ↦ exp(uA) F exp(-uB)`. -/
def clockTransportOrbit (A : E →L[ℂ] E) (B : X →L[ℂ] X) (F : X →L[ℂ] E) (u : ℂ) :
    X →L[ℂ] E :=
  NormedSpace.exp (u • A) ∘L F ∘L NormedSpace.exp ((-u) • B)

omit [CompleteSpace E] [CompleteSpace X] in
theorem clockTransportOrbit_zero (A : E →L[ℂ] E) (B : X →L[ℂ] X) (F : X →L[ℂ] E) :
    clockTransportOrbit A B F 0 = F := by
  ext x
  simp [clockTransportOrbit, NormedSpace.exp_zero]

/-- The orbit solves `F'(u) = δ F(u)`. -/
theorem hasDerivAt_clockTransportOrbit (A : E →L[ℂ] E) (B : X →L[ℂ] X) (F : X →L[ℂ] E)
    (u : ℂ) :
    HasDerivAt (clockTransportOrbit A B F) (clockTransport A B (clockTransportOrbit A B F u)) u := by
  have hA := hasDerivAt_exp_smul_const' (𝕂 := ℂ) A u
  have hB : HasDerivAt (fun v : ℂ => NormedSpace.exp ((-v) • B))
      ((-1 : ℂ) • (NormedSpace.exp ((-u) • B) * B)) u :=
    HasDerivAt.scomp u (hasDerivAt_exp_smul_const (𝕂 := ℂ) B (-u)) (hasDerivAt_neg u)
  have hFB : HasDerivAt (fun v : ℂ => F ∘L NormedSpace.exp ((-v) • B))
      (0 ∘L NormedSpace.exp ((-u) • B) + F ∘L ((-1 : ℂ) • (NormedSpace.exp ((-u) • B) * B))) u :=
    HasDerivAt.clm_comp (hasDerivAt_const u F) hB
  have h := HasDerivAt.clm_comp hA hFB
  refine HasDerivAt.congr_deriv h ?_
  ext x
  simp [clockTransport, clockTransportOrbit, sub_eq_add_neg]

theorem deriv_clockTransportOrbit (A : E →L[ℂ] E) (B : X →L[ℂ] X) (F : X →L[ℂ] E) :
    deriv (clockTransportOrbit A B F) =
      fun u => clockTransportCLM A B (clockTransportOrbit A B F u) :=
  funext fun u => (hasDerivAt_clockTransportOrbit A B F u).deriv

/-- **Third transport jet.**  The third derivative of the orbit at `0` is `J₃ = δ³ F`. -/
theorem iteratedDeriv_three_clockTransportOrbit (A : E →L[ℂ] E) (B : X →L[ℂ] X)
    (F : X →L[ℂ] E) :
    iteratedDeriv 3 (clockTransportOrbit A B F) 0 = clockTransportJet3 A B F := by
  set D := clockTransportCLM A B
  have h1 : iteratedDeriv 1 (clockTransportOrbit A B F) =
      fun u => D (clockTransportOrbit A B F u) := by
    rw [iteratedDeriv_one, deriv_clockTransportOrbit]
  have h2 : iteratedDeriv 2 (clockTransportOrbit A B F) =
      fun u => D (D (clockTransportOrbit A B F u)) := by
    rw [iteratedDeriv_succ, h1]
    funext u
    exact (HasFDerivAt.comp_hasDerivAt u D.hasFDerivAt
      (hasDerivAt_clockTransportOrbit A B F u)).deriv
  have h3 : iteratedDeriv 3 (clockTransportOrbit A B F) =
      fun u => D (D (D (clockTransportOrbit A B F u))) := by
    rw [iteratedDeriv_succ, h2]
    funext u
    exact (HasFDerivAt.comp_hasDerivAt u (D.comp D).hasFDerivAt
      (hasDerivAt_clockTransportOrbit A B F u)).deriv
  rw [h3]
  simp only [clockTransportOrbit_zero, D, clockTransportCLM_apply, clockTransportJet3]

end Orbit

/-! ## The two separating examples -/

section Examples

/-- `exp(u N) = 1 + u N` for a square-zero element. -/
theorem exp_smul_of_mul_self_eq_zero {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸]
    [CompleteSpace 𝔸] {N : 𝔸} (hN : N * N = 0) (u : ℂ) :
    NormedSpace.exp (u • N) = 1 + u • N := by
  rw [congrFun (NormedSpace.exp_eq_tsum ℂ) (u • N)]
  have hpow : ∀ n : ℕ, 2 ≤ n → (u • N) ^ n = 0 := by
    intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [pow_add, sq, smul_mul_smul_comm, hN, smul_zero, zero_mul]
  rw [tsum_eq_sum (s := Finset.range 2)]
  · simp [Finset.sum_range_succ]
  · intro n hn
    rw [Finset.mem_range, not_lt] at hn
    rw [hpow n hn, smul_zero]

/-- The nilpotent part `N(v, w) = (w, 0)` of the unipotent clock. -/
def unipotentNil : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
  ContinuousLinearMap.inl ℂ ℂ ℂ ∘L ContinuousLinearMap.snd ℂ ℂ ℂ

/-- The unipotent clock `A(v, w) = (v + w, w)`. -/
def unipotentClock : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) := 1 + unipotentNil

/-- The lift `F_h(z) = (h z, z)`. -/
def unipotentLift (h : ℂ) : ℂ →L[ℂ] (ℂ × ℂ) :=
  (h • ContinuousLinearMap.id ℂ ℂ).prod (ContinuousLinearMap.id ℂ ℂ)

theorem unipotentClock_apply (v w : ℂ) : unipotentClock (v, w) = (v + w, w) := by
  simp [unipotentClock, unipotentNil]

theorem unipotentNil_mul_self : unipotentNil * unipotentNil = 0 := by
  ext <;> simp [unipotentNil]

/-- Unipotent clock: `ω₁(z) = (z, 0)`. -/
theorem unipotent_clockTransport (h z : ℂ) :
    clockTransport unipotentClock 1 (unipotentLift h) z = (z, 0) := by
  simp [clockTransport, unipotentClock, unipotentNil, unipotentLift]

/-- Unipotent clock: `ω₃(z) = (3z, 0)`. -/
theorem unipotent_clockCubeDefect (h z : ℂ) :
    clockCubeDefect unipotentClock 1 (unipotentLift h) z = (3 * z, 0) := by
  simp [clockCubeDefect, unipotentClock, unipotentNil, unipotentLift, pow_succ]
  ring

/-- Unipotent clock: the third transport jet vanishes. -/
theorem unipotent_clockTransportJet3 (h : ℂ) :
    clockTransportJet3 unipotentClock 1 (unipotentLift h) = 0 := by
  ext <;> simp [clockTransportJet3, clockTransport, unipotentClock, unipotentNil, unipotentLift]

/-- Unipotent clock: the transport orbit is `exp(uA) F_h exp(-u)(z) = ((h + u) z, z)`. -/
theorem unipotent_clockTransportOrbit (h u z : ℂ) :
    clockTransportOrbit unipotentClock 1 (unipotentLift h) u z = ((h + u) * z, z) := by
  letI : NormedAlgebra ℚ ((ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) := NormedAlgebra.restrictScalars ℚ ℂ _
  have hA : u • unipotentClock =
      algebraMap ℂ ((ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) u + u • unipotentNil := by
    rw [unipotentClock, smul_add, Algebra.algebraMap_eq_smul_one]
  have hexpA : NormedSpace.exp (u • unipotentClock) =
      algebraMap ℂ ((ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) (NormedSpace.exp u) * (1 + u • unipotentNil) := by
    rw [hA, NormedSpace.exp_add_of_commute (Algebra.commutes u _),
      ← NormedSpace.algebraMap_exp_comm, exp_smul_of_mul_self_eq_zero unipotentNil_mul_self]
  have hexpB : NormedSpace.exp ((-u) • (1 : ℂ →L[ℂ] ℂ)) =
      algebraMap ℂ (ℂ →L[ℂ] ℂ) (NormedSpace.exp (-u)) := by
    rw [← Algebra.algebraMap_eq_smul_one, ← NormedSpace.algebraMap_exp_comm]
  have hexp : NormedSpace.exp u * NormedSpace.exp (-u) = 1 := by
    rw [← Complex.exp_eq_exp_ℂ, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have he : NormedSpace.exp u ≠ 0 := left_ne_zero_of_mul_eq_one hexp
  have hinv : NormedSpace.exp (-u) = (NormedSpace.exp u)⁻¹ := eq_inv_of_mul_eq_one_right hexp
  rw [clockTransportOrbit, hexpA, hexpB]
  simp only [ContinuousLinearMap.comp_apply, mul_apply_eq_comp,
    ContinuousLinearMap.algebraMap_apply, add_apply,
    one_apply_eq_self, smul_apply, map_smul, unipotentLift,
    unipotentNil, ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_snd',
    ContinuousLinearMap.inl_apply, ContinuousLinearMap.coe_id', id_eq]
  ext
  · simp only [Prod.smul_mk, Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    rw [hinv]; field_simp
  · simp only [Prod.smul_mk, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    rw [hinv]; field_simp; ring

/-- Unipotent clock separates: `ω₃ ≠ 0` while `J₃ = 0`. -/
theorem unipotent_cube_ne_zero_jet_eq_zero (h : ℂ) :
    clockCubeDefect unipotentClock 1 (unipotentLift h) ≠ 0 ∧
      clockTransportJet3 unipotentClock 1 (unipotentLift h) = 0 := by
  refine ⟨fun h0 => ?_, unipotent_clockTransportJet3 h⟩
  have := congrArg (fun T : ℂ →L[ℂ] (ℂ × ℂ) => (T 1).1) h0
  simp [unipotent_clockCubeDefect] at this

/-- Cube root of unity: `ω₃ = 0` while `J₃ = (ω - 1)³ ≠ 0`. -/
theorem cubeRoot_cube_eq_zero_jet_ne_zero {ω : ℂ} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    clockCubeDefect (ω • (1 : ℂ →L[ℂ] ℂ)) (1 : ℂ →L[ℂ] ℂ) (1 : ℂ →L[ℂ] ℂ) = 0 ∧
      clockTransportJet3 (ω • (1 : ℂ →L[ℂ] ℂ)) (1 : ℂ →L[ℂ] ℂ) (1 : ℂ →L[ℂ] ℂ) = (ω - 1) ^ 3 • (1 : ℂ →L[ℂ] ℂ) ∧
      clockTransportJet3 (ω • (1 : ℂ →L[ℂ] ℂ)) (1 : ℂ →L[ℂ] ℂ) (1 : ℂ →L[ℂ] ℂ) ≠ 0 := by
  have hJ : clockTransportJet3 (ω • (1 : ℂ →L[ℂ] ℂ)) (1 : ℂ →L[ℂ] ℂ) (1 : ℂ →L[ℂ] ℂ) = (ω - 1) ^ 3 • (1 : ℂ →L[ℂ] ℂ) := by
    ext
    simp [clockTransportJet3, clockTransport]
    ring
  refine ⟨?_, hJ, ?_⟩
  · ext
    simp [clockCubeDefect, smul_pow, hω3]
  · rw [hJ]
    intro h0
    have := congrArg (fun T : ℂ →L[ℂ] ℂ => T 1) h0
    simp only [smul_apply, one_apply_eq_self, smul_eq_mul,
      mul_one, zero_apply] at this
    exact hω1 (sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp this))

/-- A primitive cube root of unity exists. -/
theorem exists_cubeRoot_ne_one : ∃ ω : ℂ, ω ^ 3 = 1 ∧ ω ≠ 1 := by
  have h := Complex.isPrimitiveRoot_exp 3 (by norm_num)
  exact ⟨_, h.pow_eq_one, h.ne_one (by norm_num)⟩

/-- The powered quotient condition `A_Q³ (qF) = (qF) B³` does not force the third transport jet
to vanish (scalar example with `q = id`). -/
theorem cube_condition_not_sufficient :
    ∃ AQ : ℂ →L[ℂ] ℂ, clockCubeDefect AQ (1 : ℂ →L[ℂ] ℂ) (1 : ℂ →L[ℂ] ℂ) = 0 ∧
      clockTransportJet3 AQ (1 : ℂ →L[ℂ] ℂ) (1 : ℂ →L[ℂ] ℂ) ≠ 0 := by
  obtain ⟨ω, h3, h1⟩ := exists_cubeRoot_ne_one
  obtain ⟨hc, -, hj⟩ := cubeRoot_cube_eq_zero_jet_ne_zero h3 h1
  exact ⟨_, hc, hj⟩

end Examples

end

end GaloisForLFunctions.HTGeometry
