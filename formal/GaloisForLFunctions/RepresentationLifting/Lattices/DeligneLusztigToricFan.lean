import GaloisForLFunctions.RepresentationLifting.Lattices.RankTwoHermite

/-!
# The split Deligne–Lusztig fan as an integral lattice subdivision

The rays `(1,0), …, (1,p), (p+1,p²+p+1)` from Lemma 3.12 of
https://arxiv.org/abs/2610.40335 have unimodular adjacent pairs. The
determinant-index formula makes each adjacent lattice the full integer
lattice. Every cone lattice point is a nonnegative integral combination of adjacent
rays, and each generating ray is indecomposable. The three-ray relations
give coefficients `2, …, 2, p+2`,
the same coefficients appearing in the exceptional intersection chain.
-/

open scoped Matrix
namespace GaloisForLFunctions.RepresentationLifting.DeligneLusztigFan

/-- The fan with positive parameter `p = n+1`. -/
def ray (n k : ℕ) : Fin 2 → ℤ :=
  if k ≤ n + 1 then ![1, (k : ℤ)]
  else ![(n : ℤ) + 2, ((n : ℤ) + 1) ^ 2 + ((n : ℤ) + 1) + 1]

theorem ray_ne_zero (n k : ℕ) : ray n k ≠ 0 := by
  intro h
  have hx := congrFun h 0
  by_cases hk : k ≤ n + 1
  · exact one_ne_zero (by
      simpa only [ray, if_pos hk, Matrix.cons_val_zero, Pi.zero_apply] using hx)
  · simp only [ray, if_neg hk, Matrix.cons_val_zero, Pi.zero_apply] at hx
    omega

/-- Matrix whose columns are consecutive fan rays. -/
def adjacentMatrix (n : ℕ) (k : Fin (n + 2)) : Matrix (Fin 2) (Fin 2) ℤ :=
  ![![ray n k.val 0, ray n (k.val + 1) 0],
    ![ray n k.val 1, ray n (k.val + 1) 1]]

/-- Every cone in the subdivision is unimodular. -/
theorem adjacentMatrix_det (n : ℕ) (k : Fin (n + 2)) :
    (adjacentMatrix n k).det = 1 := by
  have hk : k.val ≤ n + 1 := by omega
  rw [Matrix.det_fin_two]
  by_cases h : k.val ≤ n
  · have hs : k.val + 1 ≤ n + 1 := by omega
    simp only [adjacentMatrix, Matrix.cons_val_zero, Matrix.cons_val_one,
      ray, if_pos hk, if_pos hs, Nat.cast_add, Nat.cast_one]
    ring
  · have he : k.val = n + 1 := by omega
    have hs : ¬ k.val + 1 ≤ n + 1 := by omega
    simp only [adjacentMatrix, Matrix.cons_val_zero, Matrix.cons_val_one,
      ray, if_pos hk, if_neg hs, he, Nat.cast_add, Nat.cast_one]
    ring

/-- Each adjacent pair generates a lattice of index one. -/
theorem adjacent_lattice_index (n : ℕ) (k : Fin (n + 2)) :
    Nat.card ((Fin 2 → ℤ) ⧸ LinearMap.range (adjacentMatrix n k).mulVecLin) = 1 := by
  rw [LinearMap.card_quotient_range_eq_natAbs_det_all]
  have hd : LinearMap.det (adjacentMatrix n k).mulVecLin = (adjacentMatrix n k).det := by
    rw [← LinearMap.det_toMatrix (Pi.basisFun ℤ (Fin 2))]
    congr 1
    rw [LinearMap.toMatrix_eq_toMatrix']
    exact (LinearEquiv.eq_symm_apply LinearMap.toMatrix').mp rfl
  rw [hd, adjacentMatrix_det, Int.natAbs_one]

/-- Interior exceptional rays satisfy the coefficient-two relation. -/
theorem interior_ray_relation (n : ℕ) (k : Fin n) :
    ray n k.val + ray n (k.val + 2) = (2 : ℤ) • ray n (k.val + 1) := by
  have h₀ : k.val ≤ n + 1 := by omega
  have h₁ : k.val + 1 ≤ n + 1 := by omega
  have h₂ : k.val + 2 ≤ n + 1 := by omega
  simp only [ray, if_pos h₀, if_pos h₁, if_pos h₂]
  ext i
  fin_cases i <;> simp <;> ring

/-- The last exceptional ray carries the larger coefficient `p+2`. -/
theorem last_ray_relation (n : ℕ) :
    ray n n + ray n (n + 2) = ((n : ℤ) + 3) • ray n (n + 1) := by
  have h₀ : n ≤ n + 1 := by omega
  have h₂ : ¬ n + 2 ≤ n + 1 := by omega
  simp only [ray, if_pos h₀, if_neg h₂, if_pos le_rfl]
  ext i
  fin_cases i <;> simp <;> ring

/-- Integer points in the cone between the first and last rays. -/
def InCone (n : ℕ) (v : Fin 2 → ℤ) : Prop :=
  0 ≤ v 0 ∧ 0 ≤ v 1 ∧
    ((n : ℤ) + 2) * v 1 ≤ (((n : ℤ) + 1) ^ 2 + ((n : ℤ) + 1) + 1) * v 0

/-- Every listed ray lies in the original rational cone. -/
theorem ray_inCone (n k : ℕ) : InCone n (ray n k) := by
  unfold InCone ray
  by_cases hk : k ≤ n + 1
  · rw [if_pos hk]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    have hkn : (k : ℤ) ≤ (n : ℤ) + 1 := by exact_mod_cast hk
    have hn : 0 ≤ (n : ℤ) := by omega
    refine ⟨by omega, by omega, ?_⟩
    have hm := mul_le_mul_of_nonneg_left hkn (show 0 ≤ (n : ℤ) + 2 by omega)
    nlinarith only [hm]
  · rw [if_neg hk]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    refine ⟨by omega, by positivity, ?_⟩
    exact le_of_eq (mul_comm _ _)

private theorem cone_add (n : ℕ) (u v : Fin 2 → ℤ)
    (hu : InCone n u) (hv : InCone n v) : InCone n (u + v) := by
  refine ⟨add_nonneg hu.1 hv.1, add_nonneg hu.2.1 hv.2.1, ?_⟩
  change ((n : ℤ) + 2) * (u 1 + v 1) ≤
    (((n : ℤ) + 1) ^ 2 + ((n : ℤ) + 1) + 1) * (u 0 + v 0)
  nlinarith only [hu.2.2, hv.2.2]

private theorem cone_smul (n : ℕ) (a : ℤ) (v : Fin 2 → ℤ)
    (ha : 0 ≤ a) (hv : InCone n v) : InCone n (a • v) := by
  refine ⟨mul_nonneg ha hv.1, mul_nonneg ha hv.2.1, ?_⟩
  change ((n : ℤ) + 2) * (a * v 1) ≤
    (((n : ℤ) + 1) ^ 2 + ((n : ℤ) + 1) + 1) * (a * v 0)
  have h := mul_le_mul_of_nonneg_left hv.2.2 ha
  nlinarith only [h]

private theorem cone_eq_zero_of_first_eq_zero (n : ℕ) (v : Fin 2 → ℤ)
    (hv : InCone n v) (hx : v 0 = 0) : v = 0 := by
  have hn : 0 ≤ (n : ℤ) := by omega
  have hb := hv.2.2
  rw [hx, mul_zero] at hb
  have hy : v 1 = 0 := by nlinarith only [hb, hv.2.1, mul_nonneg hn hv.2.1]
  ext i
  fin_cases i
  · exact hx
  · exact hy

/-- No generating ray is a sum of two nonzero integer points of the cone. -/
theorem ray_indecomposable (n k : ℕ) (u v : Fin 2 → ℤ) :
    InCone n u ∧ InCone n v ∧ ray n k = u + v → u = 0 ∨ v = 0 := by
  rintro ⟨hu, hv, he⟩
  have h₀ := congrFun he 0
  have h₁ := congrFun he 1
  by_cases hk : k ≤ n + 1
  · simp only [ray, if_pos hk, Matrix.cons_val_zero, Pi.add_apply] at h₀
    have hz : u 0 = 0 ∨ v 0 = 0 := by
      have hu0 := hu.1
      have hv0 := hv.1
      omega
    exact hz.imp (cone_eq_zero_of_first_eq_zero n u hu)
      (cone_eq_zero_of_first_eq_zero n v hv)
  · simp only [ray, if_neg hk, Matrix.cons_val_zero, Matrix.cons_val_one,
      Pi.add_apply] at h₀ h₁
    let D : ℤ := (n : ℤ) + 2
    let N : ℤ := ((n : ℤ) + 1) ^ 2 + ((n : ℤ) + 1) + 1
    have hD : 0 < D := by dsimp only [D]; omega
    have hsum : (N * u 0 - D * u 1) + (N * v 0 - D * v 1) = 0 := by
      calc
        _ = N * (u 0 + v 0) - D * (u 1 + v 1) := by ring
        _ = 0 := by rw [← h₀, ← h₁]; dsimp only [D, N]; ring
    have hδu : 0 ≤ N * u 0 - D * u 1 := sub_nonneg.mpr hu.2.2
    have hδv : 0 ≤ N * v 0 - D * v 1 := sub_nonneg.mpr hv.2.2
    have hδ : N * u 0 - D * u 1 = 0 := by linarith only [hsum, hδu, hδv]
    -- A zero boundary deficit forces the first coordinate to be a multiple of `p+1`.
    let z := u 1 - ((n : ℤ) + 1) * u 0
    have hperiod : u 0 = D * z := by
      dsimp only [N, D] at hδ
      dsimp only [D, z]
      nlinarith only [hδ]
    by_cases huz : u 0 = 0
    · exact Or.inl (cone_eq_zero_of_first_eq_zero n u hu huz)
    · have hup : 0 < u 0 := lt_of_le_of_ne hu.1 (Ne.symm huz)
      have hz : 0 < z := by
        by_contra h
        have hm := mul_le_mul_of_nonneg_left (le_of_not_gt h) hD.le
        nlinarith only [hm, hperiod, hup]
      have hz1 : 1 ≤ z := by omega
      have hm := mul_le_mul_of_nonneg_left hz1 hD.le
      have hvz : v 0 = 0 := by
        change D = u 0 + v 0 at h₀
        nlinarith only [hm, hperiod, h₀, hv.1]
      exact Or.inr (cone_eq_zero_of_first_eq_zero n v hv hvz)

/-- Every lattice point of the cone is a nonnegative integral combination of adjacent rays. -/
theorem cone_lattice_decomposition (n : ℕ) (v : Fin 2 → ℤ) :
    InCone n v ↔ ∃ k : Fin (n + 2), ∃ a b : ℤ,
      0 ≤ a ∧ 0 ≤ b ∧ v = a • ray n k.val + b • ray n (k.val + 1) := by
  constructor
  · intro hv
    let x := v 0
    let y := v 1
    have hx0 : 0 ≤ x := hv.1
    have hy0 : 0 ≤ y := hv.2.1
    have hb : ((n : ℤ) + 2) * y ≤
        (((n : ℤ) + 1) ^ 2 + ((n : ℤ) + 1) + 1) * x := hv.2.2
    have hn : 0 ≤ (n : ℤ) := by omega
    by_cases hxz : x = 0
    · have hyz : y = 0 := by
        rw [hxz, mul_zero] at hb
        nlinarith only [hy0, hb, mul_nonneg hn hy0]
      refine ⟨⟨0, by omega⟩, 0, 0, le_rfl, le_rfl, ?_⟩
      simp only [zero_smul, zero_add]
      ext i
      fin_cases i
      · exact hxz
      · exact hyz
    have hx : 0 < x := by omega
    by_cases hlo : y ≤ ((n : ℤ) + 1) * x
    -- Below slope `p`, division by `x` chooses two rays with first coordinate one.
    · let q := y / x
      let r := y % x
      have hq0 : 0 ≤ q := Int.ediv_nonneg hy0 hx.le
      have hr0 : 0 ≤ r := Int.emod_nonneg y hx.ne'
      have hrx : r < x := Int.emod_lt_of_pos y hx
      have hdiv : x * q + r = y := by
        dsimp only [q, r]
        rw [Int.emod_def]
        ring
      have hqp : q ≤ (n : ℤ) + 1 := by
        by_contra h
        have hm := mul_lt_mul_of_pos_left (lt_of_not_ge h) hx
        nlinarith only [hm, hlo, hdiv, hr0]
      by_cases hqe : q = (n : ℤ) + 1
      · have hyr : y = ((n : ℤ) + 1) * x := by
          rw [hqe] at hdiv
          nlinarith only [hdiv, hr0, hlo]
        refine ⟨⟨n + 1, by omega⟩, x, 0, hx0, le_rfl, ?_⟩
        simp only [zero_smul, add_zero, ray, if_pos le_rfl]
        ext i
        fin_cases i
        · simp [x]
        · simpa [y, mul_comm] using hyr
      · have hqn : q ≤ (n : ℤ) := by omega
        let k : Fin (n + 2) := ⟨q.toNat, by omega⟩
        have hk : k.val ≤ n + 1 := by dsimp [k]; omega
        have hks : k.val + 1 ≤ n + 1 := by dsimp [k]; omega
        have hkq : (k.val : ℤ) = q := Int.toNat_of_nonneg hq0
        refine ⟨k, x - r, r, by omega, hr0, ?_⟩
        simp only [ray, if_pos hk, if_pos hks]
        ext i
        fin_cases i
        · simp [x]
        · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_one,
            Matrix.cons_val_zero, Nat.cast_add, Nat.cast_one, hkq]
          change y = (x - r) * q + r * (q + 1)
          nlinarith only [hdiv]
    · -- The last unimodular cone gives its two coefficients directly.
      let a := (((n : ℤ) + 1) ^ 2 + ((n : ℤ) + 1) + 1) * x - ((n : ℤ) + 2) * y
      let b := y - ((n : ℤ) + 1) * x
      have ha : 0 ≤ a := sub_nonneg.mpr hb
      have hbb : 0 ≤ b := by dsimp only [b]; omega
      have hlast : ¬ n + 1 + 1 ≤ n + 1 := by omega
      refine ⟨⟨n + 1, by omega⟩, a, b, ha, hbb, ?_⟩
      simp only [ray, if_pos le_rfl, if_neg hlast]
      ext i
      fin_cases i <;>
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_one,
          Matrix.cons_val_zero, Nat.cast_add, Nat.cast_one, mul_one]
      · change x = a + b * ((n : ℤ) + 2)
        dsimp only [a, b]
        ring
      · change y = a * ((n : ℤ) + 1) + b *
          (((n : ℤ) + 1) ^ 2 + ((n : ℤ) + 1) + 1)
        dsimp only [a, b]
        ring
  · rintro ⟨k, a, b, ha, hb, rfl⟩
    exact cone_add n _ _ (cone_smul n a _ ha (ray_inCone n k.val))
      (cone_smul n b _ hb (ray_inCone n (k.val + 1)))

#print axioms adjacentMatrix_det
#print axioms adjacent_lattice_index
#print axioms interior_ray_relation
#print axioms last_ray_relation
#print axioms ray_indecomposable
#print axioms cone_lattice_decomposition

end GaloisForLFunctions.RepresentationLifting.DeligneLusztigFan
