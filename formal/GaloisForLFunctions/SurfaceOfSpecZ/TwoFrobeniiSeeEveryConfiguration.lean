import GaloisForLFunctions.SurfaceOfSpecZ.TheEffectiveClassesOfTwoFrobenii
import GaloisForLFunctions.SurfaceOfSpecZ.ARealZeroMasksTheShallowerZeros

/-!
# Two Frobenii see every configuration

For any tempered configuration the spline traces `2 Re S_Z(u)` are continuous in `u`, so a one-sided
bound on the dense lags `log m − log n`, `m, n ∈ ⟨p, q⟩`, holds at every lag
(`forall_le_two_re_lagStructure_of_twoFrobeniiLags`, `forall_two_re_lagStructure_le_of_…`), and the
criteria on all of `[0, ∞)` apply with no attainment:

* from below, without real zeros, every zero is on the line
  (`onLine_of_bddBelow_twoFrobeniiLags`); with real zeros of depth `≤ x`, every zero has depth `≤ x`
  (`re_le_of_bddBelow_twoFrobeniiLags_of_realDepth`);
* from above, in the open strip, every zero is on the line, real zeros included
  (`onLine_of_bddAbove_twoFrobeniiLags`);
* for a primitive character, an upper bound at the lags of two Frobenii is GRH for `L(s, χ)`
  (`grh_of_bddAbove_twoFrobeniiLags`), Siegel zeros included.
-/

open Filter Topology

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23

variable {p q : ℕ}

/-- The lag `log(pᵃqᵇ) − log(p^{a'}q^{b'})`. -/
def twoFrobeniiLag (p q a b a' b' : ℕ) : ℝ :=
  Real.log ((p ^ a * q ^ b : ℕ) : ℝ) - Real.log ((p ^ a' * q ^ b' : ℕ) : ℝ)

/-- A closed condition on the lags of two Frobenii holds everywhere. -/
theorem forall_of_twoFrobeniiLags (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {P : Set ℝ}
    (hP : IsClosed P) (h : ∀ a b a' b' : ℕ, twoFrobeniiLag p q a b a' b' ∈ P) (t : ℝ) : t ∈ P := by
  have hsub : ((AddSubgroup.closure {Real.log p, Real.log q} : AddSubgroup ℝ) : Set ℝ) ⊆ P := by
    intro t ht
    obtain ⟨a, b, a', b', rfl⟩ := exists_lag_of_mem_closure hp hq ht
    exact h a b a' b'
  have huniv := ((RHTower.dense_addSubgroup_log_primes hp hq hpq).mono hsub).closure_eq
  rw [hP.closure_eq] at huniv
  rw [huniv]; trivial

theorem continuous_two_re_lagStructure {Z : ZeroConfig} (hZ : TemperedConfig Z) :
    Continuous fun u : ℝ => 2 * (lagStructure Z (boxSpline 1 3) u).re :=
  continuous_const.mul (Complex.continuous_re.comp (continuous_lagStructure Z hZ
    (contDiff_boxSpline (r := 1) one_pos 2) (boxSpline_support (r := 1) one_pos 3)))

theorem forall_le_two_re_lagStructure_of_twoFrobeniiLags (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {Z : ZeroConfig} (hZ : TemperedConfig Z) {K : ℝ}
    (hK : ∀ a b a' b' : ℕ,
      -K ≤ 2 * (lagStructure Z (boxSpline 1 3) (twoFrobeniiLag p q a b a' b')).re) (u : ℝ) :
    -K ≤ 2 * (lagStructure Z (boxSpline 1 3) u).re :=
  forall_of_twoFrobeniiLags hp hq hpq (P := {u | -K ≤ 2 * (lagStructure Z (boxSpline 1 3) u).re})
    (isClosed_le continuous_const (continuous_two_re_lagStructure hZ)) hK u

theorem forall_two_re_lagStructure_le_of_twoFrobeniiLags (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {Z : ZeroConfig} (hZ : TemperedConfig Z) {K : ℝ}
    (hK : ∀ a b a' b' : ℕ,
      2 * (lagStructure Z (boxSpline 1 3) (twoFrobeniiLag p q a b a' b')).re ≤ K) (u : ℝ) :
    2 * (lagStructure Z (boxSpline 1 3) u).re ≤ K :=
  forall_of_twoFrobeniiLags hp hq hpq (P := {u | 2 * (lagStructure Z (boxSpline 1 3) u).re ≤ K})
    (isClosed_le (continuous_two_re_lagStructure hZ) continuous_const) hK u

/-- **From below at the lags of two Frobenii**, without real zeros: the line. -/
theorem onLine_of_bddBelow_twoFrobeniiLags (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (Z : ZeroConfig) (hZ : TemperedConfig Z) (hnoreal : ∀ ρ ∈ Z.carrier, ρ.im ≠ 0) {K : ℝ}
    (hK : ∀ a b a' b' : ℕ,
      -K ≤ 2 * (lagStructure Z (boxSpline 1 3) (twoFrobeniiLag p q a b a' b')).re) :
    ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 :=
  onLine_of_two_re_lagStructure_ge Z hZ hnoreal fun u _ =>
    forall_le_two_re_lagStructure_of_twoFrobeniiLags hp hq hpq hZ hK u

/-- **From below with real zeros**: every zero at or left of the deepest real zero. -/
theorem re_le_of_bddBelow_twoFrobeniiLags_of_realDepth (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (Z : ZeroConfig) (hZ : TemperedConfig Z) {x : ℝ} (hx0 : 0 ≤ x)
    (hreal : ∀ ρ ∈ Z.carrier, ρ.im = 0 → ρ.re ≤ 1 / 2 + x) {K : ℝ}
    (hK : ∀ a b a' b' : ℕ,
      -K ≤ 2 * (lagStructure Z (boxSpline 1 3) (twoFrobeniiLag p q a b a' b')).re) :
    ∀ ρ ∈ Z.carrier, ρ.re ≤ 1 / 2 + x :=
  re_le_of_two_re_lagStructure_ge_of_realDepth Z hZ hx0 hreal fun u _ =>
    forall_le_two_re_lagStructure_of_twoFrobeniiLags hp hq hpq hZ hK u

/-- **From above at the lags of two Frobenii**: the line, real zeros included. -/
theorem onLine_of_bddAbove_twoFrobeniiLags (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (Z : ZeroConfig) (hZ : TemperedConfig Z) (hlt : ∀ ρ ∈ Z.carrier, ρ.re < 1) {K : ℝ}
    (hK : ∀ a b a' b' : ℕ,
      2 * (lagStructure Z (boxSpline 1 3) (twoFrobeniiLag p q a b a' b')).re ≤ K) :
    ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 :=
  onLine_of_two_re_lagStructure_le Z hZ hlt fun u _ =>
    forall_two_re_lagStructure_le_of_twoFrobeniiLags hp hq hpq hZ hK u

/-- **GRH from above at the lags of two Frobenii**, Siegel zeros included. -/
theorem grh_of_bddAbove_twoFrobeniiLags (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {N : ℕ}
    [NeZero N] {χ : DirichletCharacter ℂ N} (hN : 1 < N) (hprim : χ.IsPrimitive) {K : ℝ}
    (hK : ∀ a b a' b' : ℕ, 2 * (lagStructure (ThmE.LZeros (ThmE.LSeam_of hN hprim)) (boxSpline 1 3)
      (twoFrobeniiLag p q a b a' b')).re ≤ K) :
    ∀ ρ ∈ (ThmE.LZeros (ThmE.LSeam_of hN hprim)).carrier, ρ.re = 1 / 2 :=
  onLine_of_bddAbove_twoFrobeniiLags hp hq hpq _ (temperedConfig_LZeros hN hprim)
    (fun _ hρ => hρ.2.2) hK

end GaloisForLFunctions.SurfaceOfSpecZ
