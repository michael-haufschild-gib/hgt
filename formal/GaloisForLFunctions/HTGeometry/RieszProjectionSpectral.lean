/-
# The range of the Riesz projection is a generalized eigenspace

If the contour encloses exactly one point of the point spectrum and the projection has
finite-dimensional range, that range is exactly the generalized eigenspace at the enclosed point:
generalized eigenvectors inside are fixed by the projection, and conversely the restriction of the
operator to the range has no eigenvalue other than the enclosed one, so over an algebraically closed
field it is the enclosed one plus a nilpotent.

Main results:
* `exists_eigenvector_of_mem_maxGenEigenspace` — a nonzero generalized eigenvector produces an
  eigenvector.
* `coe_restrict_pow`, `restrict_sub_smul` — restriction to an invariant submodule commutes with the
  algebra.
* `maxGenEigenspace_le_range_rieszProjection`, `range_rieszProjection_le_maxGenEigenspace`,
  `range_rieszProjection_eq_maxGenEigenspace` — **the range of the Riesz projection**.
-/
import GaloisForLFunctions.HTGeometry.RieszProjectionRange
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

namespace GaloisForLFunctions.HTGeometry

open Metric

/-! ## Generalized eigenvectors produce eigenvectors -/

/-- A nonzero generalized eigenvector produces an honest eigenvector for the same value. -/
theorem exists_eigenvector_of_mem_maxGenEigenspace {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] (g : Module.End K V) (μ : K) {w : V} (hw : w ≠ 0)
    (hmem : w ∈ g.maxGenEigenspace μ) : ∃ v : V, v ≠ 0 ∧ g v = μ • v := by
  classical
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace g μ w).mp hmem
  have hex : ∃ j : ℕ, ((g - μ • (1 : Module.End K V)) ^ j) w = 0 := ⟨k, hk⟩
  set j := Nat.find hex with hjdef
  have hj : ((g - μ • 1) ^ j) w = 0 := Nat.find_spec hex
  have hjpos : 0 < j := by
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · exact absurd (by simpa [h0] using hj) hw
    · exact h0
  refine ⟨((g - μ • 1) ^ (j - 1)) w, ?_, ?_⟩
  · exact fun hcon => Nat.find_min hex (by omega) hcon
  · have hstep : (g - μ • 1) (((g - μ • 1) ^ (j - 1)) w) = 0 := by
      have : (g - μ • 1) ^ j = (g - μ • 1) * (g - μ • 1) ^ (j - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      rw [this] at hj
      exact hj
    have h3 : g (((g - μ • 1) ^ (j - 1)) w) - μ • (((g - μ • 1) ^ (j - 1)) w) = 0 := hstep
    exact sub_eq_zero.mp h3

/-! ## Restriction to an invariant submodule -/

/-- The restriction of a power is the power of the restriction. -/
theorem coe_restrict_pow {K V : Type*} [CommRing K] [AddCommGroup V] [Module K V]
    {W : Submodule K V} (f : V →ₗ[K] V) (hf : ∀ x ∈ W, f x ∈ W) (k : ℕ) (x : W) :
    (((f.restrict hf) ^ k) x : V) = (f ^ k) (x : V) := by
  induction k generalizing x with
  | zero => simp
  | succ n ih =>
      have h1 : ((((f.restrict hf) ^ (n + 1)) x : W) : V)
          = f (((((f.restrict hf) ^ n) x : W) : V)) := by
        rw [pow_succ']
        rfl
      rw [h1, ih, pow_succ']
      rfl

/-- Subtracting a scalar commutes with restriction. -/
theorem restrict_sub_smul {K V : Type*} [CommRing K] [AddCommGroup V] [Module K V]
    {W : Submodule K V} (f : V →ₗ[K] V) (hf : ∀ x ∈ W, f x ∈ W) (μ : K) :
    (f.restrict hf) - μ • 1
      = (f - μ • 1).restrict (fun x hx => W.sub_mem (hf x hx) (W.smul_mem μ hx)) := by
  ext x
  simp [LinearMap.restrict_apply]

/-! ## The range of the Riesz projection -/

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- The coercion of a power of a continuous linear polynomial in `T`. -/
theorem coe_pow_sub_smul (T : H →L[ℂ] H) (lam0 : ℂ) (k : ℕ) (x : H) :
    ((T - lam0 • (1 : H →L[ℂ] H)) ^ k) x = ((((T : H →ₗ[ℂ] H) - lam0 • 1) ^ k)) x := by
  have hc : ((T - lam0 • (1 : H →L[ℂ] H) : H →L[ℂ] H) : H →ₗ[ℂ] H)
      = (T : H →ₗ[ℂ] H) - lam0 • 1 := by
    ext y; simp
  have := ContinuousLinearMap.coe_pow (T - lam0 • (1 : H →L[ℂ] H)) k
  rw [hc] at this
  exact congrFun (congrArg (fun g : H →ₗ[ℂ] H => (g : H → H)) this) x

/-- **Generalized eigenvectors for the enclosed point lie in the range of the projection.** -/
theorem maxGenEigenspace_le_range_rieszProjection {T : H →L[ℂ] H} {c : ℂ} {r : ℝ} {lam0 : ℂ}
    (hr : 0 ≤ r) (h : ∀ lam ∈ sphere c r, lam ∈ resolventSet ℂ T) (hlam0 : lam0 ∈ ball c r) :
    Module.End.maxGenEigenspace (T : H →ₗ[ℂ] H) lam0
      ≤ LinearMap.range ((rieszProjection T c r : H →L[ℂ] H) : H →ₗ[ℂ] H) := by
  intro x hx
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp hx
  exact ⟨x, rieszProjection_apply_eq_self hr h hlam0 (n := k)
    (by rw [coe_pow_sub_smul T lam0 k x]; exact hk)⟩

/-- **The range of the projection consists of generalized eigenvectors**, once the contour separates
the enclosed point from every other eigenvalue and the range is finite dimensional. -/
theorem range_rieszProjection_le_maxGenEigenspace {T : H →L[ℂ] H} {c : ℂ} {r : ℝ} {lam0 : ℂ}
    (hr : 0 ≤ r) (h : ∀ lam ∈ sphere c r, lam ∈ resolventSet ℂ T)
    (hP : rieszProjection T c r * rieszProjection T c r = rieszProjection T c r)
    (hsep : ∀ mu : ℂ, mu ≠ lam0 → (∃ v : H, v ≠ 0 ∧ T v = mu • v) → mu ∉ closedBall c r)
    (hfin : FiniteDimensional ℂ (LinearMap.range ((rieszProjection T c r : H →L[ℂ] H) : H →ₗ[ℂ] H))) :
    LinearMap.range ((rieszProjection T c r : H →L[ℂ] H) : H →ₗ[ℂ] H)
      ≤ Module.End.maxGenEigenspace (T : H →ₗ[ℂ] H) lam0 := by
  set P := rieszProjection T c r with hPdef
  set W := LinearMap.range ((P : H →L[ℂ] H) : H →ₗ[ℂ] H) with hWdef
  have hfix : ∀ x ∈ W, P x = x := by
    rintro x ⟨w, rfl⟩
    calc P (P w) = (P * P) w := rfl
      _ = P w := by rw [hP]
  have hinv : ∀ x ∈ W, (T : H →ₗ[ℂ] H) x ∈ W := by
    rintro x ⟨w, rfl⟩
    exact ⟨T w, by
      have := rieszProjection_commute T hr h
      exact congrFun (congrArg (fun g : H →L[ℂ] H => (g : H → H)) this.symm) w⟩
  set g : Module.End ℂ W := (T : H →ₗ[ℂ] H).restrict hinv with hgdef
  have hbot : ∀ mu : ℂ, mu ≠ lam0 → Module.End.maxGenEigenspace g mu = ⊥ := by
    intro mu hmu
    rw [eq_bot_iff]
    intro w hw
    by_contra hne
    obtain ⟨v, hv0, hveig⟩ := exists_eigenvector_of_mem_maxGenEigenspace g mu hne hw
    have hvH : (v : H) ≠ 0 := fun hcon => hv0 (Subtype.ext hcon)
    have hTv : T (v : H) = mu • (v : H) := by
      have := congrArg (fun y : W => (y : H)) hveig
      simpa [hgdef, LinearMap.restrict_apply] using this
    have hout : mu ∉ closedBall c r := hsep mu hmu ⟨(v : H), hvH, hTv⟩
    have hzero : P (v : H) = 0 :=
      rieszProjection_apply_eq_zero_of_eigenvector hr h hout hTv
    exact hvH (by rw [← hfix (v : H) v.2, hzero])
  have htop : Module.End.maxGenEigenspace g lam0 = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← Module.End.iSup_maxGenEigenspace_eq_top g]
    refine iSup_le fun mu => ?_
    by_cases hmu : mu = lam0
    · rw [hmu]
    · rw [hbot mu hmu]; exact bot_le
  intro x hx
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace g lam0 ⟨x, hx⟩).mp (by rw [htop]; trivial)
  refine (Module.End.mem_maxGenEigenspace _ _ _).mpr ⟨k, ?_⟩
  have hres := restrict_sub_smul (T : H →ₗ[ℂ] H) hinv lam0
  rw [hgdef, hres] at hk
  have := congrArg (fun y : W => (y : H)) hk
  rw [coe_restrict_pow] at this
  simpa using this

/-- **The range of the Riesz projection is the generalized eigenspace.** -/
theorem range_rieszProjection_eq_maxGenEigenspace {T : H →L[ℂ] H} {c : ℂ} {r : ℝ} {lam0 : ℂ}
    (hr : 0 ≤ r) (h : ∀ lam ∈ sphere c r, lam ∈ resolventSet ℂ T) (hlam0 : lam0 ∈ ball c r)
    (hP : rieszProjection T c r * rieszProjection T c r = rieszProjection T c r)
    (hsep : ∀ mu : ℂ, mu ≠ lam0 → (∃ v : H, v ≠ 0 ∧ T v = mu • v) → mu ∉ closedBall c r)
    (hfin : FiniteDimensional ℂ (LinearMap.range ((rieszProjection T c r : H →L[ℂ] H) : H →ₗ[ℂ] H))) :
    LinearMap.range ((rieszProjection T c r : H →L[ℂ] H) : H →ₗ[ℂ] H)
      = Module.End.maxGenEigenspace (T : H →ₗ[ℂ] H) lam0 :=
  le_antisymm (range_rieszProjection_le_maxGenEigenspace hr h hP hsep hfin)
    (maxGenEigenspace_le_range_rieszProjection hr h hlam0)

end GaloisForLFunctions.HTGeometry
