import GaloisForLFunctions.HTGeometry.FinitePassiveResponse

/-!
# Universal one-state finite-KMS passive palette

A countable family of one-state, zero-energy KMS/Wightman systems suffices to realize the entire
closed dissipative ray as cluster values of the imaginary response at every point of the upper
half-plane.  The amplitudes enumerate rational values; their squared norms are dense in the
nonnegative ray.  This identifies exactly what finite-system passivity contributes to a pointwise
closure criterion: the closed sign chamber, and no additional source estimate.
-/

open Topology Set

namespace HTGeometry

noncomputable section

/-- A surjective rational enumeration, cast to the real line. -/
def universalKMSRat (N : ℕ) : ℝ :=
  ((Encodable.decode (α := ℚ) N).getD 0 : ℚ)

theorem denseRange_universalKMSRat : DenseRange universalKMSRat := by
  rw [DenseRange]
  have hrange : Set.range universalKMSRat =
      Set.range (fun q : ℚ => (q : ℝ)) := by
    ext x
    constructor
    · rintro ⟨N, rfl⟩
      exact ⟨(Encodable.decode (α := ℚ) N).getD 0, rfl⟩
    · rintro ⟨q, rfl⟩
      obtain ⟨N, hN⟩ := Encodable.surjective_decode_getD ℚ 0 q
      refine ⟨N, ?_⟩
      change (((Encodable.decode (α := ℚ) N).getD 0 : ℚ) : ℝ) = (q : ℝ)
      exact congrArg (fun r : ℚ => (r : ℝ)) hN
  rw [hrange]
  exact Rat.denseRange_cast

/-- Every real square is a cluster value of the squared rational enumeration. -/
theorem sq_mem_closure_range_universalKMSRat_sq (x : ℝ) :
    x ^ 2 ∈ closure (Set.range fun N => universalKMSRat N ^ 2) := by
  have hx : x ∈ closure (Set.range universalKMSRat) :=
    denseRange_universalKMSRat x
  have himage : x ^ 2 ∈
      (fun y : ℝ => y ^ 2) '' closure (Set.range universalKMSRat) :=
    ⟨x, hx, rfl⟩
  have hcontinuous : Continuous (fun y : ℝ => y ^ 2) :=
    continuous_id.pow 2
  have hclosure := image_closure_subset_closure_image hcontinuous himage
  have hrange :
      (fun y : ℝ => y ^ 2) '' Set.range universalKMSRat =
        Set.range (fun N => universalKMSRat N ^ 2) := by
    ext y
    constructor
    · rintro ⟨_, ⟨N, rfl⟩, rfl⟩
      exact ⟨N, rfl⟩
    · rintro ⟨N, rfl⟩
      exact ⟨universalKMSRat N, ⟨N, rfl⟩, rfl⟩
  rwa [hrange] at hclosure

/-- The squared rational enumeration is dense in the nonnegative ray. -/
theorem nonneg_mem_closure_range_universalKMSRat_sq {x : ℝ} (hx : 0 ≤ x) :
    x ∈ closure (Set.range fun N => universalKMSRat N ^ 2) := by
  rw [← Real.sq_sqrt hx]
  exact sq_mem_closure_range_universalKMSRat_sq (Real.sqrt x)

/-- The zero Hamiltonian on one state. -/
def universalOneStateKMSEnergy (_N : ℕ) (_a : Fin 1) : ℝ := 0

/-- A real one-state observable whose amplitude runs through the rational enumeration. -/
def universalOneStateKMSAmplitude (N : ℕ) (_a _b : Fin 1) : ℂ :=
  universalKMSRat N

/-- The canonical KMS/Wightman transition intensity is the squared rational amplitude. -/
theorem universalOneStateKMSIntensity_eq_sq (N : ℕ) (a b : Fin 1) :
    finiteKMSWightmanTransitionIntensity 0
      (universalOneStateKMSEnergy N) (universalOneStateKMSAmplitude N) a b =
        universalKMSRat N ^ 2 := by
  simp [finiteKMSWightmanTransitionIntensity, finiteKMSWightmanWeight,
    finiteGibbsPartition, wightmanTransitionIntensity,
    universalOneStateKMSEnergy, universalOneStateKMSAmplitude,
    Complex.normSq_apply, pow_two]

/-- Exact imaginary response of the universal one-state system. -/
theorem universalOneStateKMSPassiveResponse_im (N : ℕ) (z : ℂ) :
    (finiteTransitionPassiveResponse
      (finiteKMSWightmanTransitionIntensity 0
        (universalOneStateKMSEnergy N) (universalOneStateKMSAmplitude N))
      (universalOneStateKMSEnergy N) z).im =
        -(universalKMSRat N ^ 2 * z.im) / Complex.normSq z := by
  rw [finiteTransitionPassiveResponse_im]
  simp only [Fin.sum_univ_one]
  rw [universalOneStateKMSIntensity_eq_sq]
  simp [universalOneStateKMSEnergy]

/-- Every nonpositive real number is a cluster value of the universal one-state KMS responses at
an upper-half-plane point. -/
theorem Iic_subset_closure_range_universalOneStateKMSPassiveResponse_im
    {z : ℂ} (hz : 0 < z.im) :
    Set.Iic 0 ⊆ closure (Set.range fun N =>
      (finiteTransitionPassiveResponse
        (finiteKMSWightmanTransitionIntensity 0
          (universalOneStateKMSEnergy N) (universalOneStateKMSAmplitude N))
        (universalOneStateKMSEnergy N) z).im) := by
  intro y hy
  have hz0 : z ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    linarith
  have hnorm : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz0
  let t : ℝ := -y * Complex.normSq z / z.im
  have ht : 0 ≤ t := by
    dsimp only [t]
    exact div_nonneg (mul_nonneg (neg_nonneg.mpr hy) hnorm.le) hz.le
  have htclosure :
      t ∈ closure (Set.range fun N => universalKMSRat N ^ 2) :=
    nonneg_mem_closure_range_universalKMSRat_sq ht
  let phi : ℝ → ℝ := fun u => -(u * z.im) / Complex.normSq z
  have hphi : Continuous phi := by
    fun_prop
  have hphit : phi t ∈
      phi '' closure (Set.range fun N => universalKMSRat N ^ 2) :=
    ⟨t, htclosure, rfl⟩
  have hmapped : phi t ∈ closure
      (phi '' Set.range fun N => universalKMSRat N ^ 2) :=
    image_closure_subset_closure_image hphi hphit
  have hvalue : phi t = y := by
    dsimp only [phi, t]
    field_simp [hz.ne', hnorm.ne']
  rw [hvalue] at hmapped
  have hrange :
      phi '' Set.range (fun N => universalKMSRat N ^ 2) =
        Set.range (fun N =>
          (finiteTransitionPassiveResponse
            (finiteKMSWightmanTransitionIntensity 0
              (universalOneStateKMSEnergy N) (universalOneStateKMSAmplitude N))
            (universalOneStateKMSEnergy N) z).im) := by
    ext v
    constructor
    · rintro ⟨_, ⟨N, rfl⟩, rfl⟩
      refine ⟨N, ?_⟩
      change
        (finiteTransitionPassiveResponse
          (finiteKMSWightmanTransitionIntensity 0
            (universalOneStateKMSEnergy N) (universalOneStateKMSAmplitude N))
          (universalOneStateKMSEnergy N) z).im =
            phi (universalKMSRat N ^ 2)
      rw [universalOneStateKMSPassiveResponse_im]
    · rintro ⟨N, rfl⟩
      refine ⟨universalKMSRat N ^ 2, ⟨N, rfl⟩, ?_⟩
      change
        phi (universalKMSRat N ^ 2) =
          (finiteTransitionPassiveResponse
            (finiteKMSWightmanTransitionIntensity 0
              (universalOneStateKMSEnergy N) (universalOneStateKMSAmplitude N))
            (universalOneStateKMSEnergy N) z).im
      rw [universalOneStateKMSPassiveResponse_im]
  rwa [hrange] at hmapped

/-- **Universal one-state KMS passive palette.**  At every upper-half-plane point, the cluster
set of the imaginary responses is exactly the closed dissipative ray. -/
theorem closure_range_universalOneStateKMSPassiveResponse_im
    {z : ℂ} (hz : 0 < z.im) :
    closure (Set.range fun N =>
      (finiteTransitionPassiveResponse
        (finiteKMSWightmanTransitionIntensity 0
          (universalOneStateKMSEnergy N) (universalOneStateKMSAmplitude N))
        (universalOneStateKMSEnergy N) z).im) = Set.Iic 0 := by
  apply Set.Subset.antisymm
  · apply closure_minimal
    · rintro _ ⟨N, rfl⟩
      exact finiteKMSWightmanTransitionPassiveResponse_im_nonpos
        0 (universalOneStateKMSEnergy N) (universalOneStateKMSAmplitude N) hz
    · exact isClosed_Iic
  · exact Iic_subset_closure_range_universalOneStateKMSPassiveResponse_im hz

end

end HTGeometry
