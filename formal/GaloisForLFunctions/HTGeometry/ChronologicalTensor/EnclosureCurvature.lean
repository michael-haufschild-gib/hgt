import GaloisForLFunctions.HTGeometry.ChronologicalTensor.DegreeSealing

/-!
# Curvature and strict descent of enclosed capacities

Enclosed capacities form a nonnegative log-convex sequence. Finite exact
stabilization then rules out a temporary plateau: an equality between adjacent
capacities occurs exactly at the final monotone value. The discrete second
difference is nonnegative and vanishes precisely after stabilization.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section

theorem sealedCapacity_nonneg {n r m : ℕ} (D : Fin m → Fin r → Finset (Fin n))
    (c : Fin m → ℝ) (k : ℕ) : 0 ≤ sealedCapacity D c k :=
  (abs_nonneg _).trans (sealedCapacity_probe_bound D c k (fun _ => 0))

theorem sealedCapacity_logconvex {n r m : ℕ} (D : Fin m → Fin r → Finset (Fin n))
    (c : Fin m → ℝ) (k : ℕ) :
    sealedCapacity D c (k+1)^(2 : ℕ) ≤ sealedCapacity D c k * sealedCapacity D c (k+2) := by
  let A := sealedCapacity D c k
  let B := sealedCapacity D c (k+1)
  let C := sealedCapacity D c (k+2)
  have hA : 0 ≤ A := sealedCapacity_nonneg D c k
  have hB : 0 ≤ B := sealedCapacity_nonneg D c (k+1)
  have hC : 0 ≤ C := sealedCapacity_nonneg D c (k+2)
  have hb : B ≤ Real.sqrt (A*C) := by
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨g,rfl⟩
    dsimp only
    rw [abs_mul,abs_pow]
    apply Real.le_sqrt_of_sq_le
    have hl := sealedCapacity_probe_bound D c k g
    have hr := sealedCapacity_probe_bound D c (k+2) g
    rw [abs_mul,abs_pow] at hl hr
    have hm := mul_le_mul hl hr (by positivity) hA
    have hid : (|displacement (normalizeProbe g)|^(k+1)*|familyValue D c (normalizeProbe g)|)^(2 : ℕ) =
        (|displacement (normalizeProbe g)|^k*|familyValue D c (normalizeProbe g)|)*
        (|displacement (normalizeProbe g)|^(k+2)*|familyValue D c (normalizeProbe g)|) := by
      simp only [pow_add,pow_one,pow_two]
      ring
    rw [hid]
    exact hm
  have hs := Real.sq_sqrt (mul_nonneg hA hC)
  have hn := Real.sqrt_nonneg (A*C)
  change B^(2 : ℕ) ≤ A*C
  nlinarith only [hb,hB,hs,hn]

theorem sealedCapacity_plateau_iff {n r m : ℕ} (D : Fin m → Fin r → Finset (Fin (n+1)))
    (c : Fin m → ℝ) (k : ℕ) :
    sealedCapacity D c k = sealedCapacity D c (k+1) ↔
      sealedCapacity D c k = monotoneCapacity D c := by
  constructor
  · intro hEq
    let C := sealedCapacity D c k
    have hC0 : 0 ≤ C := sealedCapacity_nonneg D c k
    by_cases hz : C = 0
    · have hm0 := monotoneCapacity_nonneg D c
      have hml := monotoneCapacity_le_sealed D c k
      change C = monotoneCapacity D c
      change monotoneCapacity D c ≤ C at hml
      linarith only [hz,hm0,hml]
    have hC : 0 < C := lt_of_le_of_ne hC0 (Ne.symm hz)
    have hconst : ∀ j : ℕ, sealedCapacity D c (k+j) = C ∧
        sealedCapacity D c (k+j+1) = C := by
      intro j
      induction j with
      | zero =>
        simp only [Nat.add_zero]
        exact ⟨rfl,hEq.symm⟩
      | succ j ih =>
        have hcurve := sealedCapacity_logconvex D c (k+j)
        rw [ih.1,ih.2] at hcurve
        have hle := sealedCapacity_add_depth D c k (j+2)
        have he : k+(j+2) = k+j+2 := by omega
        rw [he] at hle
        have hnext : sealedCapacity D c (k+j+2) = C := by
          change sealedCapacity D c (k+j+2) ≤ C at hle
          nlinarith only [hcurve,hle,hC]
        constructor
        · simpa only [Nat.add_succ] using ih.2
        · exact hnext
    obtain ⟨N,hN⟩ := eventual_exact_sealing D c
    have hstop := hN k
    have hfixed := (hconst N).1
    rw [Nat.add_comm N k] at hstop
    exact hfixed.symm.trans hstop
  · intro hEq
    have hupper := sealedCapacity_add_depth D c k 1
    have hlower := monotoneCapacity_le_sealed D c (k+1)
    linarith only [hEq,hupper,hlower]

theorem sealedCapacity_strict_drop_iff {n r m : ℕ} (D : Fin m → Fin r → Finset (Fin (n+1)))
    (c : Fin m → ℝ) (k : ℕ) :
    sealedCapacity D c (k+1) < sealedCapacity D c k ↔
      monotoneCapacity D c < sealedCapacity D c k := by
  constructor
  · intro h
    exact (monotoneCapacity_le_sealed D c (k+1)).trans_lt h
  · intro h
    have hm := sealedCapacity_add_depth D c k 1
    apply lt_of_le_of_ne hm
    intro he
    have hx := (sealedCapacity_plateau_iff D c k).mp he.symm
    linarith only [hx,h]

def enclosureCurvature {n r m : ℕ} (D : Fin m → Fin r → Finset (Fin n))
    (c : Fin m → ℝ) (k : ℕ) : ℝ :=
  sealedCapacity D c k - 2*sealedCapacity D c (k+1) + sealedCapacity D c (k+2)

theorem enclosureCurvature_nonneg {n r m : ℕ} (D : Fin m → Fin r → Finset (Fin n))
    (c : Fin m → ℝ) (k : ℕ) : 0 ≤ enclosureCurvature D c k := by
  have h := sealedCapacity_logconvex D c k
  have h0 := sealedCapacity_nonneg D c k
  have h1 := sealedCapacity_nonneg D c (k+1)
  have h2 := sealedCapacity_nonneg D c (k+2)
  unfold enclosureCurvature
  nlinarith only [h,h0,h1,h2,sq_nonneg (sealedCapacity D c k-sealedCapacity D c (k+2))]

theorem enclosureCurvature_zero_iff {n r m : ℕ} (D : Fin m → Fin r → Finset (Fin (n+1)))
    (c : Fin m → ℝ) (k : ℕ) :
    enclosureCurvature D c k = 0 ↔ sealedCapacity D c k = monotoneCapacity D c := by
  constructor
  · intro he
    have hcurve := sealedCapacity_logconvex D c k
    have hmono := sealedCapacity_add_depth D c k 1
    apply (sealedCapacity_plateau_iff D c k).mp
    unfold enclosureCurvature at he
    have he2 : sealedCapacity D c (k+2) = 2*sealedCapacity D c (k+1)-sealedCapacity D c k := by
      linarith only [he]
    rw [he2] at hcurve
    nlinarith only [hcurve,hmono,sq_nonneg (sealedCapacity D c k-sealedCapacity D c (k+1))]
  · intro he
    have h1 := (sealedCapacity_plateau_iff D c k).mpr he
    have he1 : sealedCapacity D c (k+1) = monotoneCapacity D c := h1.symm.trans he
    have h2 := (sealedCapacity_plateau_iff D c (k+1)).mpr he1
    unfold enclosureCurvature
    have hn : k+1+1 = k+2 := by omega
    rw [hn] at h2
    linarith only [h1,h2]

theorem enclosureCurvature_pos_iff {n r m : ℕ} (D : Fin m → Fin r → Finset (Fin (n+1)))
    (c : Fin m → ℝ) (k : ℕ) :
    0 < enclosureCurvature D c k ↔ monotoneCapacity D c < sealedCapacity D c k := by
  have h0 := enclosureCurvature_nonneg D c k
  have hm := monotoneCapacity_le_sealed D c k
  have he := enclosureCurvature_zero_iff D c k
  constructor
  · intro h
    by_contra hn
    have hx : sealedCapacity D c k = monotoneCapacity D c := by linarith only [hm,hn]
    have hz := he.mpr hx
    linarith only [h,hz]
  · intro h
    by_contra hn
    have hz : enclosureCurvature D c k = 0 := by linarith only [h0,hn]
    have hx := he.mp hz
    linarith only [h,hx]

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
