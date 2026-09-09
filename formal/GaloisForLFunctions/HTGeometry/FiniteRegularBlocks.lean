import GaloisForLFunctions.HTGeometry.FiniteRegularGeneratorCost

/-!
# Uniform variance control by two complete subgroup averages

Every motion in a finite subgroup is bounded by twice the distance to its
Reynolds average. Four alternating subgroup factors therefore control the
complete finite regular variance by sixteen times the two block variances.
The estimate retains all coordinates and is independent of group cardinality.
-/

namespace GaloisForLFunctions.HTGeometry.FiniteRegularBlocks
open HTGeometry.ConstraintRelativity FiniteRegularGeneratorCost
open scoped BigOperators
noncomputable section
variable {G : Type*} [Group G] [Fintype G]
variable {H : Type*} [Group H] [Fintype H]
variable {K : Type*} [Group K] [Fintype K]

def blockUnitary (p : H →* G) (h : H) : EuclideanSpace ℂ G ≃ₗᵢ[ℂ] EuclideanSpace ℂ G :=
  finiteRegularUnitary (p h)

omit [Fintype H] in
theorem blockUnitary_mul (p : H →* G) (h k : H) :
    blockUnitary p (h*k)=(blockUnitary p k).trans (blockUnitary p h) := by
  simp only [blockUnitary,map_mul,finiteRegularUnitary_mul]

/-- Average over the entire finite subgroup image, with uniform fibre multiplicities. -/
def blockAverage (p : H →* G) (v : EuclideanSpace ℂ G) : EuclideanSpace ℂ G :=
  reynolds (blockUnitary p) v

theorem blockAverage_fixed (p : H →* G) (v : EuclideanSpace ℂ G) (h : H) :
    finiteRegularUnitary (p h) (blockAverage p v)=blockAverage p v :=
  reynolds_fixed (blockUnitary p) (blockUnitary_mul p) v h

theorem blockAverage_norm_decomposition (p : H →* G) (v : EuclideanSpace ℂ G) :
    ‖blockAverage p v‖^2+‖v-blockAverage p v‖^2=‖v‖^2 := by
  have h := inner_reynolds_self (blockUnitary p) (blockUnitary_mul p) v
  change inner ℂ (blockAverage p v) (blockAverage p v)=inner ℂ (blockAverage p v) v at h
  have hr : ‖blockAverage p v‖^2=(inner ℂ (blockAverage p v) v).re := by
    rw [← h]
    exact (inner_self_eq_norm_sq (𝕜:=ℂ) _).symm
  have hn := norm_sub_sq (𝕜:=ℂ) (blockAverage p v) v
  rw [norm_sub_rev,show RCLike.re (inner ℂ (blockAverage p v) v)=
    (inner ℂ (blockAverage p v) v).re from rfl,← hr] at hn
  linarith

/-- Exact normalized block displacement energy equals its orthogonal variance. -/
theorem blockAverage_energy (p : H →* G) (v : EuclideanSpace ℂ G) :
    (2*(Fintype.card H:ℝ))⁻¹*(∑ h : H, ‖finiteRegularUnitary (p h) v-v‖^2)=
      ‖v-blockAverage p v‖^2 := by
  have he := reynolds_energy (blockUnitary p) (blockUnitary_mul p) v
  have hn := blockAverage_norm_decomposition p v
  change (2*(Fintype.card H:ℝ))⁻¹*(∑ h : H, ‖finiteRegularUnitary (p h) v-v‖^2)=
    ‖v‖^2-‖blockAverage p v‖^2 at he
  linarith

/-- Every motion inside one block costs at most twice the distance to its average. -/
theorem displacement_le_block_complement (p : H →* G) (v : EuclideanSpace ℂ G) (h : H) :
    ‖finiteRegularUnitary (p h) v-v‖ ≤ 2*‖v-blockAverage p v‖ := by
  calc
    ‖finiteRegularUnitary (p h) v-v‖ =
        ‖finiteRegularUnitary (p h) (v-blockAverage p v)-(v-blockAverage p v)‖ := by
      rw [map_sub,blockAverage_fixed]
      congr 1
      abel
    _ ≤ ‖finiteRegularUnitary (p h) (v-blockAverage p v)‖+‖v-blockAverage p v‖ := norm_sub_le _ _
    _ = _ := by rw [LinearIsometryEquiv.norm_map]; ring

/-- Four alternating full blocks give a cardinality-independent displacement bound. -/
theorem four_block_displacement_le (p : H →* G) (q : K →* G)
    (v : EuclideanSpace ℂ G) (a c : H) (b d : K) :
    ‖finiteRegularUnitary (p a*q b*p c*q d) v-v‖ ≤
      4*(‖v-blockAverage p v‖+‖v-blockAverage q v‖) := by
  have h1 := displacement_mul_le (p a*q b*p c) (q d) v
  have h2 := displacement_mul_le (p a*q b) (p c) v
  have h3 := displacement_mul_le (p a) (q b) v
  have ha := displacement_le_block_complement p v a
  have hb := displacement_le_block_complement q v b
  have hc := displacement_le_block_complement p v c
  have hd := displacement_le_block_complement q v d
  linarith

/-- Bounded full-block factorization controls complete regular variance with constant 16. -/
theorem variance_le_two_blocks (p : H →* G) (q : K →* G)
    (hfac : ∀ g : G, ∃ a : H, ∃ b : K, ∃ c : H, ∃ d : K, g=p a*q b*p c*q d)
    (v : EuclideanSpace ℂ G) :
    ‖v-finiteRegularAverage v‖^2 ≤
      16*(‖v-blockAverage p v‖^2+‖v-blockAverage q v‖^2) := by
  have hb (g : G) : ‖finiteRegularUnitary g v-v‖^2 ≤
      32*(‖v-blockAverage p v‖^2+‖v-blockAverage q v‖^2) := by
    obtain ⟨a,b,c,d,rfl⟩ := hfac g
    have h := four_block_displacement_le p q v a c b d
    have ha := norm_nonneg (v-blockAverage p v)
    have hc := norm_nonneg (v-blockAverage q v)
    have hd := norm_nonneg (finiteRegularUnitary (p a*q b*p c*q d) v-v)
    nlinarith [sq_nonneg (‖v-blockAverage p v‖-‖v-blockAverage q v‖)]
  have hs := Finset.sum_le_sum (fun g (_ : g ∈ (Finset.univ : Finset G)) => hb g)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hs
  have hcard : 0 < (Fintype.card G:ℝ) := by exact_mod_cast Fintype.card_pos
  have he := finiteRegularAverage_energy v
  have hn := finiteRegularAverage_norm_decomposition v
  have he' : (∑ g : G, ‖finiteRegularUnitary g v-v‖^2)=
      2*(Fintype.card G:ℝ)*‖v-finiteRegularAverage v‖^2 := by
    rw [inv_mul_eq_iff_eq_mul₀ (by positivity)] at he
    nlinarith
  rw [he'] at hs
  nlinarith

end
end GaloisForLFunctions.HTGeometry.FiniteRegularBlocks
