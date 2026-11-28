import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.DepthZeroJacquetInjective
import Mathlib.Analysis.SpecificLimits.Basic

/-! Vanishing of the opposite Jacquet module forces the finite
forward radical to have no fixed vector. Each Jacquet relation is
killed in principal-congruence coinvariants sufficiently far along
the contracting projection torus. -/

noncomputable section

open Matrix Representation GlobalTheory.OppRad Filter Topology

namespace GlobalTheory.GLp

variable {p n : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ (GL (Fin n) ℚ_[p]) V)

local notation "φ" => RingHom.mapMatrix (m := Fin n) (PadicInt.toZMod (p := p))
local notation "ι" => RingHom.mapMatrix (m := Fin n) (algebraMap ℤ_[p] ℚ_[p])
local notation "K" => principalCongruenceOne p (Fin n)
local notation "r" => MonoidHom.comp ρ (Subgroup.subtype K)

theorem eventually_projectionTorus_conj_mem_principalCongruenceOne
    {P : Matrix (Fin n) (Fin n) ℤ_[p]} (hP : P * P = P)
    (u : GL (Fin n) ℚ_[p]) (hu : u ∈ U (1 - ι P) (ι P)) :
    ∀ᶠ m : ℕ in atTop, projectionTorus hP m * u * (projectionTorus hP m)⁻¹ ∈ K := by
  let A := ι P
  let B := u.val - 1
  have hAB : A * B = 0 := by
    have h : (1 - A) * B = B := hu.1
    rw [sub_mul, one_mul, sub_eq_self] at h
    exact h
  have hBA : B * A = B := hu.2
  have h : ∀ m : ℕ,
      ((projectionTorus hP m * u * (projectionTorus hP m)⁻¹).val - 1) =
        (p : ℚ_[p]) ^ m • B := by
    intro m
    let d := projectionTorus hP m
    have he : (d * u * d⁻¹).val - 1 = d.val * (u.val - 1) * (d⁻¹).val := by
      rw [mul_sub, sub_mul, mul_one, Units.mul_inv]
      rfl
    rw [he]
    change (A + (p : ℚ_[p]) ^ m • (1 - A)) * B *
      (A + ((p : ℚ_[p]) ^ m)⁻¹ • (1 - A)) = _
    rw [add_mul, hAB, smul_mul_assoc, sub_mul, one_mul, hAB, sub_zero, zero_add,
      smul_mul_assoc, mul_add, hBA, mul_smul_comm, mul_sub, mul_one, hBA, sub_self,
      smul_zero, add_zero]
  have hp : ‖(p : ℚ_[p])‖ < 1 := by
    rw [Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  have hb (i j : Fin n) : Tendsto (fun m : ℕ => ‖(p : ℚ_[p])‖ ^ m * ‖B i j‖) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg (p : ℚ_[p])) hp).mul tendsto_const_nhds
  have he (i j : Fin n) : ∀ᶠ m : ℕ in atTop, ‖(p : ℚ_[p])‖ ^ m * ‖B i j‖ < 1 :=
    (hb i j).eventually (gt_mem_nhds zero_lt_one)
  filter_upwards [Filter.eventually_all.2 (fun i => Filter.eventually_all.2 (he i))] with m hm
  apply (mem_principalCongruenceOne_iff p (Fin n) _).mpr
  intro i j
  rw [h, Matrix.smul_apply, smul_eq_mul, norm_mul, norm_pow]
  exact hm i j

theorem eventually_projectionTorus_mem_coinvariantKer
    {P : Matrix (Fin n) (Fin n) ℤ_[p]} (hP : P * P = P)
    {v : V} (hv : v ∈ Coinvariants.ker (ρ.comp (U (1 - ι P) (ι P)).subtype)) :
    ∀ᶠ m : ℕ in atTop, ρ (projectionTorus hP m) v ∈ Coinvariants.ker r := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨⟨u, w⟩, rfl⟩ := hv
    filter_upwards [eventually_projectionTorus_conj_mem_principalCongruenceOne hP u.val u.2] with m hm
    let d := projectionTorus hP m
    let a : K := ⟨d * u.val * d⁻¹, hm⟩
    change ρ d (ρ u.val w - w) ∈ Coinvariants.ker r
    have he : ρ d (ρ u.val w) = r a (ρ d w) := by
      change ρ d (ρ u.val w) = ρ (d * u.val * d⁻¹) (ρ d w)
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
    rw [map_sub, he]
    exact Coinvariants.sub_mem_ker a (ρ d w)
  | zero => exact Eventually.of_forall fun m => by rw [map_zero]; exact (Coinvariants.ker r).zero_mem
  | add u v _ _ hu hv =>
    filter_upwards [hu, hv] with m h1 h2
    rw [map_add]
    exact (Coinvariants.ker r).add_mem h1 h2
  | smul c v _ hv =>
    filter_upwards [hv] with m hm
    rw [map_smul]
    exact (Coinvariants.ker r).smul_mem c hm

theorem eq_zero_of_residueRadical_fixed
    (hρ : ∀ v : V, IsOpen {g : GL (Fin n) ℚ_[p] | ρ g v = v})
    {P : Matrix (Fin n) (Fin n) ℤ_[p]} (hP : P * P = P)
    (hJ : Coinvariants.ker (ρ.comp (U (1 - ι P) (ι P)).subtype) = ⊤)
    (v : principalFixed ρ)
    (hv : ∀ u ∈ U (φ P) (1 - φ P), principalFixedReduction ρ u v = v) :
    v = 0 := by
  have hvJ : v.val ∈ Coinvariants.ker (ρ.comp (U (1 - ι P) (ι P)).subtype) := hJ ▸ Submodule.mem_top
  obtain ⟨m, hm⟩ := (eventually_projectionTorus_mem_coinvariantKer ρ hP hvJ).exists
  exact eq_zero_of_projectionTorus_mem_coinvariantKer ρ hρ hP m v hv hm

end GlobalTheory.GLp

#print axioms GlobalTheory.GLp.eq_zero_of_residueRadical_fixed
