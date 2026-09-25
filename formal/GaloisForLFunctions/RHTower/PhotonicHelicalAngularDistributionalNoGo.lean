import GaloisForLFunctions.RHTower.PhotonicPassiveMultimodeFluxNoGo

/-!
# Distributional helical angular no-go

A jointly polynomial-growth two-index Fourier field cannot solve the real-frequency,
positive-loss helical angular recurrence. The proof uses the conserved charge
`q = ℓ - m*n` and the grade-dependent passive-flux law. This is an angular-only
model: no radial/interface boundary flux or square-lattice mode mixing is present.
-/

namespace RHTower

open Complex
open scoped InnerProductSpace

private theorem ptr_complex_inner_self (x : ℂ) :
    (inner ℂ x x).re = ‖x‖ ^ 2 := by
  rw [inner_self_eq_norm_sq_to_K]
  simpa using (RCLike.re_ofReal_pow (K := ℂ) ‖x‖ 2)

/-- Polynomial growth of squared joint Fourier coefficients. -/
def ptrJointSquarePolyGrowth (c : ℤ → ℤ → ℂ) : Prop :=
  ∃ C : ℝ, ∃ d : ℕ, 0 ≤ C ∧
    ∀ n ℓ : ℤ, ‖c n ℓ‖ ^ 2 ≤
      C * (1 + |(n : ℝ)| + |(ℓ : ℝ)|) ^ d

private theorem ptr_joint_growth_shear_forward
    (c : ℤ → ℤ → ℂ) (m : ℤ)
    (hjoint : ptrJointSquarePolyGrowth c) :
    ptrJointSquarePolyGrowth (fun n q => c n (q + m*n)) := by
  obtain ⟨C,d,hC,hbound⟩ := hjoint
  let D : ℝ := 1 + |(m : ℝ)|
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨C * D ^ d, d, by positivity, ?_⟩
  intro n q
  have hqm : |(((q + m*n : ℤ) : ℝ))| ≤
      |(q : ℝ)| + |(m : ℝ)| * |(n : ℝ)| := by
    calc
      |(((q + m*n : ℤ) : ℝ))| = |(q : ℝ) + (m : ℝ)*(n : ℝ)| := by
        simp only [Int.cast_add, Int.cast_mul]
      _ ≤ |(q : ℝ)| + |(m : ℝ)*(n : ℝ)| := abs_add_le _ _
      _ = |(q : ℝ)| + |(m : ℝ)| * |(n : ℝ)| := by rw [abs_mul]
  have hbase : 1 + |(n : ℝ)| + |(((q + m*n : ℤ) : ℝ))| ≤
      D * (1 + |(n : ℝ)| + |(q : ℝ)|) := by
    dsimp [D]
    have hrem : 0 ≤ |(m : ℝ)| * (1 + |(q : ℝ)|) := by positivity
    nlinarith only [hqm, hrem]
  calc
    ‖c n (q + m*n)‖ ^ 2 ≤
        C * (1 + |(n : ℝ)| + |(((q + m*n : ℤ) : ℝ))|) ^ d :=
          hbound n (q + m*n)
    _ ≤ C * (D * (1 + |(n : ℝ)| + |(q : ℝ)|)) ^ d := by gcongr
    _ = C * D ^ d * (1 + |(n : ℝ)| + |(q : ℝ)|) ^ d := by
      rw [mul_pow]
      ring

/-- Joint Fourier polynomial growth is invariant under the integer helical
shear `ℓ = q + m*n`. This is the positive structural survivor of the no-go. -/
theorem ptr_helical_shear_joint_growth_iff
    (c : ℤ → ℤ → ℂ) (m : ℤ) :
    ptrJointSquarePolyGrowth (fun n q => c n (q + m*n)) ↔
      ptrJointSquarePolyGrowth c := by
  constructor
  · intro h
    have h' := ptr_joint_growth_shear_forward
      (fun n q => c n (q + m*n)) (-m) h
    change ptrJointSquarePolyGrowth
      (fun n q => c n ((q + (-m)*n) + m*n)) at h'
    have heq : (fun n q => c n ((q + (-m)*n) + m*n)) = c := by
      funext n q
      congr 1
      ring
    rw [heq] at h'
    exact h'
  · exact ptr_joint_growth_shear_forward c m

private theorem scalar_grade_loss_no_go
    (z : ℤ → ℂ) (k nu : ℤ → ℝ) (eps a gamma : ℝ)
    (ha : 0 < a) (hgamma : 0 < gamma) (hnu : ∀ n, nu n ≠ 0)
    (hrec : ∀ n : ℤ,
      (((nu n)^2 : ℝ) : ℂ) *
        (((eps : ℂ) + I * (gamma : ℂ)) * z n +
          (a : ℂ) * z (n-1) + (a : ℂ) * z (n+1)) =
        (k n : ℂ) * z n)
    (hpoly : ∀ j : ℤ, ∃ A : ℝ, ∃ d : ℕ, ∀ N : ℕ,
      RHTower.ptrSymMass (fun n => ‖z (n+j)‖ ^ 2) N
        ≤ A * (1 + (N : ℝ)) ^ d) :
    ∀ n, z n = 0 := by
  let H : ℤ → ℂ →ₗ[ℂ] ℂ := fun n => (k n : ℂ) • LinearMap.id
  let M0 : ℂ →ₗ[ℂ] ℂ := (eps : ℂ) • LinearMap.id
  let Mp : ℂ →ₗ[ℂ] ℂ := (a : ℂ) • LinearMap.id
  let G : ℂ →ₗ[ℂ] ℂ := LinearMap.id
  have hH : ∀ n x, (inner ℂ x (H n x)).im = 0 := by
    intro n x
    simp [H]
    ring
  have hM0 : ∀ x, (inner ℂ x (M0 x)).im = 0 := by
    intro x
    simp [M0]
    ring
  have hG : ∀ x, 0 ≤ (inner ℂ x (G x)).re := by
    intro x
    change 0 ≤ (inner ℂ x x).re
    rw [ptr_complex_inner_self]
    positivity
  have hAdj : ∀ x y, inner ℂ x (Mp y) =
      starRingEnd ℂ (inner ℂ y (Mp x)) := by
    intro x y
    have h := RHTower.ptr_factorized_helical_adjoint_pair
      (ContinuousLinearMap.id ℂ ℂ) (ContinuousLinearMap.id ℂ ℂ) a x y
    simpa [Mp] using h
  have hBound : ∀ x y, |(inner ℂ x (Mp y)).im| ≤
      (a / 2) * ((inner ℂ x (G x)).re + (inner ℂ y (G y)).re) := by
    intro x y
    have h := RHTower.ptr_factorized_helical_form_bound
      (ContinuousLinearMap.id ℂ ℂ) (ContinuousLinearMap.id ℂ ℂ)
      a (le_of_lt ha) (by simp) x y
    simpa [Mp, G] using h
  have hrec' : ∀ n : ℤ,
      (((nu n)^2 : ℝ) : ℂ) •
        (M0 (z n) + Mp (z (n-1)) + Mp (z (n+1)) +
          (I * (gamma : ℂ)) • G (z n)) = H n (z n) := by
    intro n
    simpa [H, M0, Mp, G, smul_eq_mul, mul_add, add_mul,
      add_assoc, add_left_comm, add_comm] using hrec n
  have hpoly' : ∀ j : ℤ, ∃ A : ℝ, ∃ d : ℕ, ∀ N : ℕ,
      RHTower.ptrSymMass
        (fun n => (inner ℂ (z (n+j)) (G (z (n+j)))).re) N
          ≤ A * (1 + (N : ℝ)) ^ d := by
    intro j
    obtain ⟨A,d,hp⟩ := hpoly j
    refine ⟨A,d,?_⟩
    intro N
    have hf : (fun n => (inner ℂ (z (n+j)) (G (z (n+j)))).re) =
        (fun n => ‖z (n+j)‖ ^ 2) := by
      funext n
      change (inner ℂ (z (n+j)) (z (n+j))).re = _
      exact ptr_complex_inner_self _
    rw [hf]
    exact hp N
  have hz := RHTower.ptr_passive_multimode_grade_spatial_loss_overlap_zero
    H M0 Mp Mp G z nu gamma (a / 2) hgamma (by positivity) hnu
    hH hM0 hG hAdj hBound hrec' hpoly'
  intro n
  have hnorm : ‖z n‖ ^ 2 = 0 := by
    have hh : (inner ℂ (z n) (z n)).re = 0 := hz n
    rw [ptr_complex_inner_self] at hh
    exact hh
  have : ‖z n‖ = 0 := by nlinarith [norm_nonneg (z n)]
  exact norm_eq_zero.mp this

/-- A joint helical recurrence has no nonzero polynomial-mass charge sector.
This is an angular model; radial and interface boundary flux are absent. -/
theorem ptr_angular_helical_sector_no_go
    (c : ℤ → ℤ → ℂ) (m : ℤ) (nu : ℤ → ℝ)
    (eps a gamma : ℝ) (ha : 0 < a) (hgamma : 0 < gamma)
    (hnu : ∀ n, nu n ≠ 0)
    (hrec : ∀ n ℓ : ℤ,
      (((nu n)^2 : ℝ) : ℂ) *
        (((eps : ℂ) + I * (gamma : ℂ)) * c n ℓ +
          (a : ℂ) * c (n-1) (ℓ-m) +
          (a : ℂ) * c (n+1) (ℓ+m)) =
        (((ℓ : ℝ)^2 : ℝ) : ℂ) * c n ℓ)
    (hgrowth : ∃ C : ℝ, ∃ d : ℕ, 0 ≤ C ∧
      ∀ n q : ℤ, ‖c n (q + m*n)‖ ^ 2 ≤
        C * (1 + |(n : ℝ)| + |(q : ℝ)|) ^ d) :
    ∀ n ℓ, c n ℓ = 0 := by
  intro n ℓ
  let q : ℤ := ℓ - m*n
  let z : ℤ → ℂ := fun j => c j (q + m*j)
  have hsrec : ∀ j : ℤ,
      (((nu j)^2 : ℝ) : ℂ) *
        (((eps : ℂ) + I * (gamma : ℂ)) * z j +
          (a : ℂ) * z (j-1) + (a : ℂ) * z (j+1)) =
        (((((q + m*j : ℤ) : ℝ)^2 : ℝ) : ℂ)) * z j := by
    intro j
    have hjm : q + m*j - m = q + m*(j-1) := by ring
    have hjp : q + m*j + m = q + m*(j+1) := by ring
    have h := hrec j (q + m*j)
    rw [hjm, hjp] at h
    simpa [z] using h
  obtain ⟨C,d,hC,hcoeff⟩ := hgrowth
  have hspoly : ∀ j : ℤ, ∃ A : ℝ, ∃ e : ℕ, ∀ N : ℕ,
      RHTower.ptrSymMass (fun v => ‖z (v+j)‖ ^ 2) N
        ≤ A * (1 + (N : ℝ)) ^ e := by
    intro j
    let D : ℝ := 1 + |(j : ℝ)| + |(q : ℝ)|
    have hD : 0 ≤ D := by dsimp [D]; positivity
    refine ⟨3 * C * D ^ d, d + 1, ?_⟩
    intro N
    have hterm : ∀ v ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        ‖z (v+j)‖ ^ 2 ≤ C * D ^ d * (1 + (N : ℝ)) ^ d := by
      intro v hv
      have hvabs : |(v : ℝ)| ≤ (N : ℝ) := by
        have hvl : -(N : ℤ) ≤ v := (Finset.mem_Icc.mp hv).1
        have hvu : v ≤ (N : ℤ) := (Finset.mem_Icc.mp hv).2
        have hvlr : -(N : ℝ) ≤ (v : ℝ) := by exact_mod_cast hvl
        have hvur : (v : ℝ) ≤ (N : ℝ) := by exact_mod_cast hvu
        exact abs_le.mpr ⟨hvlr, hvur⟩
      have hjabs : |((v+j : ℤ) : ℝ)| ≤ |(v : ℝ)| + |(j : ℝ)| := by
        simpa only [Int.cast_add] using abs_add_le (v : ℝ) (j : ℝ)
      have hbase : 1 + |((v+j : ℤ) : ℝ)| + |(q : ℝ)| ≤
          D * (1 + (N : ℝ)) := by
        dsimp [D]
        have hq0 : 0 ≤ |(q : ℝ)| := abs_nonneg _
        have hj0 : 0 ≤ |(j : ℝ)| := abs_nonneg _
        nlinarith [mul_nonneg (show 0 ≤ |(j : ℝ)| + |(q : ℝ)| by positivity)
          (show 0 ≤ (N : ℝ) by positivity)]
      calc
        ‖z (v+j)‖ ^ 2 ≤ C * (1 + |(((v+j):ℤ) : ℝ)| + |(q : ℝ)|) ^ d := by
          exact hcoeff (v+j) q
        _ ≤ C * (D * (1 + (N : ℝ))) ^ d := by gcongr
        _ = C * D ^ d * (1 + (N : ℝ)) ^ d := by rw [mul_pow]; ring
    have hcard : (Finset.Icc (-(N : ℤ)) (N : ℤ)).card = 2 * N + 1 := by
      rw [Int.card_Icc]
      omega
    have hsum : RHTower.ptrSymMass (fun v => ‖z (v+j)‖ ^ 2) N ≤
        (2 * (N : ℝ) + 1) * (C * D ^ d * (1 + (N : ℝ)) ^ d) := by
      unfold RHTower.ptrSymMass
      calc
        (∑ v ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ‖z (v+j)‖ ^ 2) ≤
          ∑ _v ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
            C * D ^ d * (1 + (N : ℝ)) ^ d := by
              apply Finset.sum_le_sum
              intro v hv
              exact hterm v hv
        _ = (2 * (N : ℝ) + 1) * (C * D ^ d * (1 + (N : ℝ)) ^ d) := by
          simp [hcard]
    calc
      RHTower.ptrSymMass (fun v => ‖z (v+j)‖ ^ 2) N ≤
          (2 * (N : ℝ) + 1) * (C * D ^ d * (1 + (N : ℝ)) ^ d) := hsum
      _ ≤ (3 * C * D ^ d) * (1 + (N : ℝ)) ^ (d + 1) := by
        have hN : 0 ≤ (N : ℝ) := by positivity
        have hB : 0 ≤ C * D ^ d * (1 + (N : ℝ)) ^ d := by positivity
        have hlin : 2 * (N : ℝ) + 1 ≤ 3 * (1 + (N : ℝ)) := by linarith
        have hmul := mul_le_mul_of_nonneg_right hlin hB
        rw [pow_succ]
        nlinarith
  have hz := scalar_grade_loss_no_go z
    (fun j => ((q + m*j : ℤ) : ℝ)^2) nu eps a gamma
    ha hgamma hnu hsrec hspoly n
  simpa [z, q, sub_add_cancel_left] using hz

/-- No nonzero jointly polynomial-growth Fourier distribution solves the
positive-loss helical angular recurrence on the spacetime torus. -/
theorem ptr_angular_helical_joint_tempered_no_go
    (c : ℤ → ℤ → ℂ) (m : ℤ) (nu : ℤ → ℝ)
    (eps a gamma : ℝ) (ha : 0 < a) (hgamma : 0 < gamma)
    (hnu : ∀ n, nu n ≠ 0)
    (hrec : ∀ n ℓ : ℤ,
      (((nu n)^2 : ℝ) : ℂ) *
        (((eps : ℂ) + I * (gamma : ℂ)) * c n ℓ +
          (a : ℂ) * c (n-1) (ℓ-m) +
          (a : ℂ) * c (n+1) (ℓ+m)) =
        (((ℓ : ℝ)^2 : ℝ) : ℂ) * c n ℓ)
    (hjoint : ptrJointSquarePolyGrowth c) :
    ∀ n ℓ, c n ℓ = 0 := by
  have hshear := ptr_joint_growth_shear_forward c m hjoint
  exact ptr_angular_helical_sector_no_go c m nu eps a gamma
    ha hgamma hnu hrec hshear

end RHTower
