import GaloisForLFunctions.HTGeometry.MultivariateEntireCommMonoid
import GaloisForLFunctions.HTGeometry.FlatMultiplier

/-!
# The packet-indexed flat multiplier

`AbeDampingPacketData.seed_jet` quantifies over every packet index, so the damping multiplier must be
the identity on the jets at **each** packet point.  One normalized profile per point, combined as
`1 − ∏ⱼ (1 − Θⱼ)^{mⱼ}`, achieves that: at the `k`-th point the `k`-th factor vanishes to order `m k`,
so the whole product does, while the value is `1` there.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- The monoid power agrees with the explicit power of entire sources. -/
theorem multivariateEntire_pow_eq {d : ℕ} (f : MultivariateEntire d) (n : ℕ) :
    f ^ n = multivariateEntirePow f n := by
  induction n with
  | zero =>
      ext x
      rw [pow_zero, multivariateEntirePow_apply, pow_zero, multivariateEntire_one_apply]
  | succ n ih =>
      ext x
      rw [pow_succ, multivariateEntire_mul_apply, ih, multivariateEntirePow_apply,
        multivariateEntirePow_apply, pow_succ]

/-- The packet-indexed flat multiplier. -/
def packetFlatMultiplier {d : ℕ} {J : Type*} [Fintype J] [DecidableEq J]
    (Θ : J → MultivariateEntire d) (m : J → ℕ) : MultivariateEntire d :=
  1 - ∏ j : J, (1 - Θ j) ^ (m j)

theorem packetFlatMultiplier_apply {d : ℕ} {J : Type*} [Fintype J] [DecidableEq J]
    (Θ : J → MultivariateEntire d) (m : J → ℕ) (x : Fin d → ℂ) :
    (packetFlatMultiplier Θ m).1 x = 1 - ∏ j : J, (1 - (Θ j).1 x) ^ (m j) := by
  rw [packetFlatMultiplier]
  have hsub : ∀ (f g : MultivariateEntire d) (y : Fin d → ℂ), (f - g).1 y = f.1 y - g.1 y :=
    fun _ _ _ => rfl
  rw [hsub, multivariateEntire_one_apply, multivariateEntire_prod_apply]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [multivariateEntire_pow_eq, multivariateEntirePow_apply, hsub,
    multivariateEntire_one_apply]

/-- **An invariant family gives an invariant packet multiplier.** -/
theorem packetFlatMultiplier_invariant {d : ℕ} {J : Type*} [Fintype J] [DecidableEq J]
    (Θ : J → MultivariateEntire d) (m : J → ℕ) {ΓH : AddSubgroup (Fin d → ℂ)}
    (hΘ : ∀ j, ∀ η ∈ ΓH, ∀ x, (Θ j).1 (x + η) = (Θ j).1 x) :
    ∀ η ∈ ΓH, ∀ x, (packetFlatMultiplier Θ m).1 (x + η)
      = (packetFlatMultiplier Θ m).1 x := by
  intro η hη x
  rw [packetFlatMultiplier_apply, packetFlatMultiplier_apply]
  congr 1
  exact Finset.prod_congr rfl fun j _ => by rw [hΘ j η hη x]

/-- **The packet multiplier does not move the low jets at any normalization point.** -/
theorem multiIndexJetEvalCLM_packetFlatMultiplier_mul {d : ℕ} {J : Type*} [Fintype J]
    [DecidableEq J] (Θ : J → MultivariateEntire d) (m : J → ℕ) (f : MultivariateEntire d)
    (k : J) {p : Fin d → ℂ} (hΘ : (Θ k).1 p = 1) (a : Fin d →₀ ℕ)
    (ha : Finsupp.degree a < m k) :
    multiIndexJetEvalCLM p a (multivariateEntireMul (packetFlatMultiplier Θ m) f)
      = multiIndexJetEvalCLM p a f := by
  classical
  set h : MultivariateEntire d := 1 - Θ k with hh
  set rest : MultivariateEntire d :=
    ∏ j ∈ (Finset.univ : Finset J).erase k, (1 - Θ j) ^ (m j) with hrest
  have hhp : h.1 p = 0 := by
    show (1 : MultivariateEntire d).1 p - (Θ k).1 p = 0
    rw [multivariateEntire_one_apply, hΘ, sub_self]
  have hsplit : multivariateEntireMul (packetFlatMultiplier Θ m) f
      = f - multivariateEntireMul (multivariateEntirePow h (m k))
        (multivariateEntireMul rest f) := by
    ext x
    rw [multivariateEntireMul_apply, packetFlatMultiplier_apply]
    have hsub : ∀ (u v : MultivariateEntire d) (y : Fin d → ℂ), (u - v).1 y = u.1 y - v.1 y :=
      fun _ _ _ => rfl
    rw [hsub, multivariateEntireMul_apply, multivariateEntirePow_apply,
      multivariateEntireMul_apply]
    have hprod : ∏ j : J, (1 - (Θ j).1 x) ^ (m j)
        = (1 - (Θ k).1 x) ^ (m k) * ∏ j ∈ (Finset.univ : Finset J).erase k,
            (1 - (Θ j).1 x) ^ (m j) :=
      (Finset.mul_prod_erase (Finset.univ : Finset J)
        (fun j => (1 - (Θ j).1 x) ^ (m j)) (Finset.mem_univ k)).symm
    have hhx : h.1 x = 1 - (Θ k).1 x := by
      show (1 : MultivariateEntire d).1 x - (Θ k).1 x = 1 - (Θ k).1 x
      rw [multivariateEntire_one_apply]
    have hrestx : rest.1 x = ∏ j ∈ (Finset.univ : Finset J).erase k,
        (1 - (Θ j).1 x) ^ (m j) := by
      rw [hrest, multivariateEntire_prod_apply]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [multivariateEntire_pow_eq, multivariateEntirePow_apply]
      congr 1
      show (1 : MultivariateEntire d).1 x - (Θ j).1 x = 1 - (Θ j).1 x
      rw [multivariateEntire_one_apply]
    rw [hprod, hhx, hrestx]
    ring
  rw [hsplit, map_sub,
    multiIndexJetEvalCLM_mul_pow_eq_zero_of_degree_lt h (multivariateEntireMul rest f) p hhp a ha,
    sub_zero]

end

end GaloisForLFunctions.HTGeometry
