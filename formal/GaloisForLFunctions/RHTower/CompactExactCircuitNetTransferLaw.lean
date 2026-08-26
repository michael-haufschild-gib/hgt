import GaloisForLFunctions.RHTower.ExactContinuousCircuitResidualReplicaRankLaw
import GaloisForLFunctions.RHTower.PairQubitProjectiveResidualDesignCubicFirstReturnLaw
import GaloisForLFunctions.HTGeometry.OrdinaryTwoLocalGaussianHarmonicChoiGrowthLaw

open scoped BigOperators Matrix Matrix.Norms.L2Operator
open Matrix Set Metric

namespace RHTower

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw
open GaloisForLFunctions.HTGeometry.OrdinaryTwoLocalGaussianHarmonicChoiGrowthLaw

noncomputable section

/-- A disjoint union of endpoint dictionaries costs at most the sum of their occupied ranks. -/
theorem finrank_replicaTargetSpan_sum_le_add
    {C D alpha : Type*} [Fintype alpha]
    (r : ℕ) (targetC : C → alpha → ℂ) (targetD : D → alpha → ℂ) :
    Module.finrank ℂ
        (replicaTargetSpan r (Sum.elim targetC targetD)) ≤
      Module.finrank ℂ (replicaTargetSpan r targetC) +
        Module.finrank ℂ (replicaTargetSpan r targetD) := by
  have hspan : replicaTargetSpan r (Sum.elim targetC targetD) =
      replicaTargetSpan r targetC ⊔ replicaTargetSpan r targetD := by
    unfold replicaTargetSpan
    rw [show (fun c => finitePureTensorPowerEuclidean r
        ((Sum.elim targetC targetD) c)) =
      Sum.elim (fun c => finitePureTensorPowerEuclidean r (targetC c))
        (fun c => finitePureTensorPowerEuclidean r (targetD c)) by
      funext c
      cases c <;> rfl]
    rw [Set.Sum.elim_range, Submodule.span_union]
  rw [hspan]
  exact Submodule.finrank_add_le_finrank_add_finrank _ _

/-- Exact-depth continuous two-qubit circuit image is nonempty on every register with two sites. -/
theorem circuitImageExact_nonempty_of_two_le
    {n : ℕ} (hn : 2 ≤ n) (s : ℕ) :
    (TwoQubitArchitecture.circuitImageExact n s).Nonempty := by
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  have hab : a ≠ b := by
    intro h
    have := congrArg Fin.val h
    norm_num [a, b] at this
  let A : TwoQubitArchitecture n s :=
    ⟨fun _ => (a, b), fun _ => hab⟩
  let gates : Fin s → Matrix.specialUnitaryGroup (Bool × Bool) ℂ := fun _ => 1
  refine ⟨A.contraction gates, ?_⟩
  rw [TwoQubitArchitecture.circuitImageExact]
  simp only [Set.mem_iUnion, Set.mem_range]
  exact ⟨A, gates, rfl⟩

/-- Every complete exact-depth circuit image admits an arbitrarily fine finite net of actual endpoints. -/
theorem exists_finite_internal_exactCircuitNet
    {n s : ℕ} (hn : 2 ≤ n) {eps : ℝ} (heps : 0 < eps) :
    ∃ net : Set (Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ),
      net ⊆ TwoQubitArchitecture.circuitImageExact n s ∧
      net.Finite ∧ net.Nonempty ∧
      ∀ U ∈ TwoQubitArchitecture.circuitImageExact n s,
        ∃ V ∈ net, dist U V < eps := by
  let K := TwoQubitArchitecture.circuitImageExact n s
  obtain ⟨net, hnetK, hfinite, hcover⟩ :=
    (TwoQubitArchitecture.isCompact_circuitImageExact n s).finite_cover_balls heps
  have hKne : K.Nonempty := circuitImageExact_nonempty_of_two_le hn s
  have hnetne : net.Nonempty := by
    obtain ⟨U, hUK⟩ := hKne
    have hUcover := hcover hUK
    simp only [Set.mem_iUnion, Metric.mem_ball] at hUcover
    obtain ⟨V, hVnet, -⟩ := hUcover
    exact ⟨V, hVnet⟩
  refine ⟨net, hnetK, hfinite, hnetne, ?_⟩
  intro U hUK
  have hUcover := hcover hUK
  simp only [Set.mem_iUnion, Metric.mem_ball] at hUcover
  obtain ⟨V, hVnet, hdist⟩ := hUcover
  exact ⟨V, hVnet, hdist⟩

/-- Eigenbasis transport and normalized Choi embedding do not amplify endpoint operator distance. -/
theorem norm_choiVector_hermitianSpectralEndpoint_sub_le
    {d : ℕ} (hd : 0 < d) {H : Matrix (Fin d) (Fin d) ℂ} (hH : H.IsHermitian)
    (U V : Matrix.unitaryGroup (Fin d) ℂ) :
    ‖GaloisForLFunctions.RHTower.choiVector
        (hermitianSpectralEndpoint hH U : Matrix (Fin d) (Fin d) ℂ) -
      GaloisForLFunctions.RHTower.choiVector
        (hermitianSpectralEndpoint hH V : Matrix (Fin d) (Fin d) ℂ)‖ ≤
      ‖(U : Matrix (Fin d) (Fin d) ℂ) -
        (V : Matrix (Fin d) (Fin d) ℂ)‖ := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  have hchoi : GaloisForLFunctions.RHTower.choiVector
        (hermitianSpectralEndpoint hH U : Matrix (Fin d) (Fin d) ℂ) -
      GaloisForLFunctions.RHTower.choiVector
        (hermitianSpectralEndpoint hH V : Matrix (Fin d) (Fin d) ℂ) =
      GaloisForLFunctions.RHTower.choiVector
        ((hermitianSpectralEndpoint hH U : Matrix (Fin d) (Fin d) ℂ) -
          (hermitianSpectralEndpoint hH V : Matrix (Fin d) (Fin d) ℂ)) := by
    ext p
    simp [GaloisForLFunctions.RHTower.choiVector]
    ring
  rw [hchoi]
  refine (norm_choiVector_le_l2_opNorm _).trans ?_
  let K := hH.eigenvectorUnitary
  have hmatrix :
      (hermitianSpectralEndpoint hH U : Matrix (Fin d) (Fin d) ℂ) -
          (hermitianSpectralEndpoint hH V : Matrix (Fin d) (Fin d) ℂ) =
        star (K : Matrix (Fin d) (Fin d) ℂ) *
          ((U : Matrix (Fin d) (Fin d) ℂ) -
            (V : Matrix (Fin d) (Fin d) ℂ)) *
          (K : Matrix (Fin d) (Fin d) ℂ) := by
    dsimp [hermitianSpectralEndpoint, K]
    noncomm_ring
  rw [hmatrix]
  calc
    ‖star (K : Matrix (Fin d) (Fin d) ℂ) *
        ((U : Matrix (Fin d) (Fin d) ℂ) -
          (V : Matrix (Fin d) (Fin d) ℂ)) *
        (K : Matrix (Fin d) (Fin d) ℂ)‖ ≤
      ‖star (K : Matrix (Fin d) (Fin d) ℂ)‖ *
        ‖(U : Matrix (Fin d) (Fin d) ℂ) -
          (V : Matrix (Fin d) (Fin d) ℂ)‖ *
        ‖(K : Matrix (Fin d) (Fin d) ℂ)‖ := by
      exact (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ = ‖(U : Matrix (Fin d) (Fin d) ℂ) -
          (V : Matrix (Fin d) (Fin d) ℂ)‖ := by
      rw [norm_star]
      have hK : ‖(K : Matrix (Fin d) (Fin d) ℂ)‖ = 1 :=
        CStarRing.norm_coe_unitary K
      rw [hK]
      ring

/-- The canonical finite-coordinate endpoint reindex is an operator-norm isometry on differences. -/
theorem norm_finiteGaussianHermitianPencilReindexedEndpoint_sub_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (U V : Matrix.unitaryGroup ι ℂ) :
    ‖(finiteGaussianHermitianPencilReindexedEndpoint U :
        Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ) -
      (finiteGaussianHermitianPencilReindexedEndpoint V :
        Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ)‖ =
      ‖(U : Matrix ι ι ℂ) - (V : Matrix ι ι ℂ)‖ := by
  change ‖Matrix.reindexAlgEquiv ℂ ℂ (Fintype.equivFin ι)
      (U : Matrix ι ι ℂ) -
    Matrix.reindexAlgEquiv ℂ ℂ (Fintype.equivFin ι)
      (V : Matrix ι ι ℂ)‖ = _
  rw [← map_sub, norm_reindexAlgEquiv_eq]

/-- Finite-net exclusion transfers to an arbitrary target class with only the net radius added. -/
theorem no_innerCapture_of_finiteNet
    {T C W alpha : Type*} [Fintype alpha]
    (state : T → EuclideanSpace ℂ alpha)
    (hstate : ∀ t, ‖state t‖ = 1)
    (target : C → EuclideanSpace ℂ alpha)
    (net : W → EuclideanSpace ℂ alpha) (netIndex : C → W)
    {threshold radius : ℝ}
    (hnet : ∀ c, ‖target c - net (netIndex c)‖ ≤ radius)
    (hno : ¬ ∃ t, ∃ w, threshold ≤ ‖inner ℂ (state t) (net w)‖) :
    ¬ ∃ t, ∃ c, threshold + radius ≤
      ‖inner ℂ (state t) (target c)‖ := by
  rintro ⟨t, c, hhit⟩
  apply hno
  refine ⟨t, netIndex c, ?_⟩
  have hinner :
      ‖inner ℂ (state t) (target c)‖ ≤
        ‖inner ℂ (state t) (net (netIndex c))‖ + radius := by
    calc
      ‖inner ℂ (state t) (target c)‖ =
          ‖inner ℂ (state t) (net (netIndex c)) +
            inner ℂ (state t) (target c - net (netIndex c))‖ := by
        congr 1
        rw [inner_sub_right]
        abel
      _ ≤ ‖inner ℂ (state t) (net (netIndex c))‖ +
          ‖inner ℂ (state t) (target c - net (netIndex c))‖ := norm_add_le _ _
      _ ≤ ‖inner ℂ (state t) (net (netIndex c))‖ +
          ‖state t‖ * ‖target c - net (netIndex c)‖ := by
        gcongr
        exact norm_inner_le_norm _ _
      _ ≤ ‖inner ℂ (state t) (net (netIndex c))‖ + radius := by
        rw [hstate]
        simpa using add_le_add_left (hnet c) ‖inner ℂ (state t) (net (netIndex c))‖
  linarith

end

end RHTower
