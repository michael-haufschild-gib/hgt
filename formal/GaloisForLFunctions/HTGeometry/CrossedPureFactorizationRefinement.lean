import GaloisForLFunctions.HTGeometry.DecomposableTensorRigidity

/-!
# Crossed pure factorizations force a common refinement

Suppose a nonzero four-index tensor has two crossed decomposable presentations:

`x i j * y k l = u i k * v j l`.

Then the first presentation already refines into four one-index factors.  The proof chooses one
nonzero coordinate in each of `x` and `y` and contracts the crossed equality along those
coordinates.

This is elementary Segre-tensor rigidity and standard multipartite pure-state separability
structure.  It does not select the four index types, construct physical subsystems, handle mixed
states, or derive spacetime.
-/

namespace GaloisForLFunctions.HTGeometry

variable {𝕜 : Type*} [Field 𝕜]
variable {I J K L : Type*}

/--
If the same nonzero four-index tensor factorizes across `IJ | KL` and `IK | JL`, then the two
blocks in the first factorization split across the common four-block refinement.
-/
theorem crossedBlockFactorization_refines
    {x : I → J → 𝕜} {y : K → L → 𝕜}
    {u : I → K → 𝕜} {v : J → L → 𝕜}
    (hx : x ≠ 0) (hy : y ≠ 0)
    (hcross : ∀ i j k l, x i j * y k l = u i k * v j l) :
    ∃ a : I → 𝕜, ∃ b : J → 𝕜, ∃ c : K → 𝕜, ∃ d : L → 𝕜,
      (∀ i j, x i j = a i * b j) ∧
      (∀ k l, y k l = c k * d l) := by
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 hx
  obtain ⟨j₀, hij₀⟩ := Function.ne_iff.1 hi₀
  obtain ⟨k₀, hk₀⟩ := Function.ne_iff.1 hy
  obtain ⟨l₀, hkl₀⟩ := Function.ne_iff.1 hk₀
  refine ⟨fun i => u i k₀, fun j => v j l₀ / y k₀ l₀,
    fun k => u i₀ k / x i₀ j₀, fun l => v j₀ l, ?_, ?_⟩
  · intro i j
    dsimp
    rw [← mul_div_assoc]
    exact (eq_div_iff hkl₀).2 (hcross i j k₀ l₀)
  · intro k l
    dsimp
    rw [div_mul_eq_mul_div]
    exact (eq_div_iff hij₀).2 (by
      simpa [mul_comm] using hcross i₀ j₀ k l)

/--
The common four-index tensor itself is a product of four one-index factors.
-/
theorem crossedPureFactorization_refines_to_four
    {x : I → J → 𝕜} {y : K → L → 𝕜}
    {u : I → K → 𝕜} {v : J → L → 𝕜}
    (hx : x ≠ 0) (hy : y ≠ 0)
    (hcross : ∀ i j k l, x i j * y k l = u i k * v j l) :
    ∃ a : I → 𝕜, ∃ b : J → 𝕜, ∃ c : K → 𝕜, ∃ d : L → 𝕜,
      ∀ i j k l, x i j * y k l = a i * b j * c k * d l := by
  obtain ⟨a, b, c, d, hx', hy'⟩ :=
    crossedBlockFactorization_refines hx hy hcross
  refine ⟨a, b, c, d, ?_⟩
  intro i j k l
  rw [hx' i j, hy' k l]
  ring

end GaloisForLFunctions.HTGeometry
