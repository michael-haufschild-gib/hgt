import GaloisForLFunctions.RHTower.DeningerMeyerComplete
import GaloisForLFunctions.RHTower.DeningerMeyerTopology
import GaloisForLFunctions.RHTower.DeningerOscMeyerDomination

/-!
# The Meyer source is complete

Unlike the `C^r` seminorms of the circle, the Meyer seminorms `q_{A,n}` are monotone only in the
exponent, so finite suprema do not collapse to a single index.  They still reduce to finitely many
single-index conditions, which is all the Cauchy and convergence translations need.

* `DeningerMeyerSource.instCompleteSpace` : **`H_-` is complete.**
-/

namespace RHTower

open Filter Topology Uniformity GaloisForLFunctions

/-- **The Meyer source is complete.** -/
noncomputable instance DeningerMeyerSource.instCompleteSpace :
    CompleteSpace DeningerMeyerSource := by
  haveI hcg : (𝓤 DeningerMeyerSource).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_zero]
    infer_instance
  refine UniformSpace.complete_of_cauchySeq_tendsto fun u hu => ?_
  have huni : (𝓤 DeningerMeyerSource).HasBasis
      (fun sr : Finset (ℕ × ℕ) × ℝ => 0 < sr.2)
      (fun sr => (fun q : DeningerMeyerSource × DeningerMeyerSource => q.2 - q.1) ⁻¹'
        ((sr.1.sup DeningerMeyerSource.seminorms).ball 0 sr.2)) := by
    rw [uniformity_eq_comap_nhds_zero]
    exact DeningerMeyerSource.withSeminorms.hasBasis_zero_ball.comap _
  rw [huni.cauchySeq_iff] at hu
  -- single-index Cauchy condition
  have hcauchy : ∀ (A : ℝ) (n : ℕ) (ε : ℝ), 0 < ε → ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ N,
      deningerMeyerSeminormFun A n
        (DeningerMeyerSource.toSource (u p) - DeningerMeyerSource.toSource (u q)) < ε := by
    intro A n ε hε
    obtain ⟨M, hM⟩ := exists_nat_ge A
    obtain ⟨N, hN⟩ := hu ({(M, n)}, ε) hε
    refine ⟨N, fun p hp q hq => ?_⟩
    have hmem := hN q hq p hp
    have hlt : (({(M, n)} : Finset (ℕ × ℕ)).sup DeningerMeyerSource.seminorms) (u p - u q) < ε :=
      (Seminorm.mem_ball_zero _).1 hmem
    rw [Finset.sup_singleton] at hlt
    exact lt_of_le_of_lt (deningerMeyerSeminormFun_mono hM n _) hlt
  obtain ⟨G, hG⟩ :=
    deningerExpSchwartz_exists_limit (fun k => DeningerMeyerSource.toSource (u k)) hcauchy
  refine ⟨DeningerMeyerSource.toSource.symm G, ?_⟩
  rw [← tendsto_sub_nhds_zero_iff,
    DeningerMeyerSource.withSeminorms.hasBasis_zero_ball.tendsto_right_iff]
  rintro ⟨s, ε⟩ hε
  have hε' : (0 : ℝ) < ε := hε
  have hpiece : ∀ i ∈ s, ∀ᶠ k in atTop,
      DeningerMeyerSource.seminorms i (u k - DeningerMeyerSource.toSource.symm G) ≤ ε / 2 := by
    intro i _
    obtain ⟨N, hN⟩ := hG ((i.1 : ℕ) : ℝ) i.2 (ε / 2) (by linarith)
    exact Filter.eventually_atTop.2 ⟨N, fun k hk => hN k hk⟩
  have hall : ∀ᶠ k in atTop, ∀ i ∈ s,
      DeningerMeyerSource.seminorms i (u k - DeningerMeyerSource.toSource.symm G) ≤ ε / 2 :=
    (Filter.eventually_all_finset s).2 hpiece
  refine hall.mono fun k hk => ?_
  refine (Seminorm.mem_ball_zero _).2 ?_
  refine lt_of_le_of_lt (deningerFinsetSup_apply_le DeningerMeyerSource.seminorms s _
    (by linarith) hk) (by linarith)

end RHTower
