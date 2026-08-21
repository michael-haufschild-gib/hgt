/-
# A separating direction of the diagonal carrier

Base-three onsite weights and equal edge couplings make the classical Ising energies of the path
carrier pairwise distinct, with a gap that survives the whole edge contribution as soon as the
onsite scale exceeds the number of edges.  Every edge coupling of the direction is the same
positive number, so the strong-bond condition holds on it by construction.

Main results:
* `sepCarrier` — the base-three carrier direction.
* `pathDiagEnergy_sepCarrier` — its classical energies.
* `abs_sub_pathDiagEnergy_sepCarrier_ge` — **the energies are separated**.
-/
import GaloisForLFunctions.HTGeometry.PathDiagonalCarrier
import GaloisForLFunctions.HTGeometry.BaseThreeSignSeparation
import GaloisForLFunctions.HTGeometry.DiagonalPatchConstruction

open Matrix Finset
open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {n : ℕ}

theorem zSetSign_singleton_eq (s : Fin (n + 2)) (x : FiniteQubitConfiguration (Fin (n + 2))) :
    zSetSign ({s} : Finset (Fin (n + 2))) x = siteSign x s := by
  rw [zSetSign, Finset.prod_singleton, siteSign]

theorem zSetSign_pair_eq (e : Fin (n + 1)) (x : FiniteQubitConfiguration (Fin (n + 2))) :
    zSetSign ({e.castSucc, e.succ} : Finset (Fin (n + 2))) x
      = siteSign x e.castSucc * siteSign x e.succ := by
  have hne : e.castSucc ≠ e.succ := (Fin.castSucc_lt_succ (i := e)).ne
  rw [zSetSign, Finset.prod_pair hne, siteSign, siteSign]

/-- The base-three carrier direction: onsite `Z` weights `A·3^s`, every edge coupling `b`. -/
def sepCarrier (n : ℕ) (A b : ℝ) : PathShell n :=
  WithLp.toLp 2 fun l =>
    match l with
    | Sum.inl sq => if sq.2 = 2 then A * 3 ^ (sq.1 : ℕ) else 0
    | Sum.inr eab => if eab.2 = (2, 2) then b else 0

theorem sepCarrier_offDiag (A b : ℝ) (l : PathLabel n) (hl : ¬ IsDiagLabel l) :
    sepCarrier n A b l = 0 := by
  cases l with
  | inl sq =>
      have : sq.2 ≠ 2 := by simpa [IsDiagLabel] using hl
      show (if sq.2 = 2 then A * 3 ^ (sq.1 : ℕ) else 0) = 0
      rw [if_neg this]
  | inr eab =>
      have : eab.2 ≠ (2, 2) := by simpa [IsDiagLabel] using hl
      show (if eab.2 = (2, 2) then b else 0) = 0
      rw [if_neg this]

theorem sepCarrier_onsite (A b : ℝ) (s : Fin (n + 2)) :
    sepCarrier n A b (Sum.inl (s, 2)) = A * 3 ^ (s : ℕ) := by
  show (if (2 : Fin 3) = 2 then A * 3 ^ (s : ℕ) else 0) = _
  rw [if_pos rfl]

theorem sepCarrier_edge (A b : ℝ) (e : Fin (n + 1)) :
    sepCarrier n A b (Sum.inr (e, (2, 2))) = b := by
  show (if ((2 : Fin 3), (2 : Fin 3)) = (2, 2) then b else 0) = _
  rw [if_pos rfl]

theorem pathDiagEnergy_sepCarrier (A b : ℝ) (x : FiniteQubitConfiguration (Fin (n + 2))) :
    pathDiagEnergy (sepCarrier n A b) x
      = (∑ s : Fin (n + 2), A * 3 ^ (s : ℕ) * siteSign x s)
        + ∑ e : Fin (n + 1), b * (siteSign x e.castSucc * siteSign x e.succ) := by
  rw [pathDiagEnergy]
  congr 1
  · exact Finset.sum_congr rfl fun s _ => by
      rw [sepCarrier_onsite, zSetSign_singleton_eq]
  · exact Finset.sum_congr rfl fun e _ => by
      rw [sepCarrier_edge, zSetSign_pair_eq]

/-- **The carrier energies are separated.**  Once the onsite scale exceeds the edge scale times the
number of edges, distinct configurations have distinct energies, with an explicit gap. -/
theorem abs_sub_pathDiagEnergy_sepCarrier_ge {A b : ℝ} (hA : 0 ≤ A) (hb : 0 ≤ b)
    {x y : FiniteQubitConfiguration (Fin (n + 2))} (hxy : x ≠ y) :
    2 * A - 2 * b * ((n : ℝ) + 1)
      ≤ |pathDiagEnergy (sepCarrier n A b) x - pathDiagEnergy (sepCarrier n A b) y| := by
  classical
  have honsite : (∑ s : Fin (n + 2), A * 3 ^ (s : ℕ) * siteSign x s)
      - ∑ s : Fin (n + 2), A * 3 ^ (s : ℕ) * siteSign y s
      = A * ∑ s : Fin (n + 2), (3 : ℝ) ^ (s : ℕ) * (siteSign x s - siteSign y s) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring
  have hbase := two_le_abs_sum_signDiff hxy
  have honsite_ge : 2 * A ≤ |(∑ s : Fin (n + 2), A * 3 ^ (s : ℕ) * siteSign x s)
      - ∑ s : Fin (n + 2), A * 3 ^ (s : ℕ) * siteSign y s| := by
    rw [honsite, abs_mul, abs_of_nonneg hA]
    nlinarith [hbase, hA]
  have hedge : |(∑ e : Fin (n + 1), b * (siteSign x e.castSucc * siteSign x e.succ))
      - ∑ e : Fin (n + 1), b * (siteSign y e.castSucc * siteSign y e.succ)|
      ≤ 2 * b * ((n : ℝ) + 1) := by
    rw [← Finset.sum_sub_distrib]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hterm : ∀ e ∈ (Finset.univ : Finset (Fin (n + 1))),
        |b * (siteSign x e.castSucc * siteSign x e.succ)
          - b * (siteSign y e.castSucc * siteSign y e.succ)| ≤ 2 * b := by
      intro e _
      have hx1 := abs_siteSign x e.castSucc
      have hx2 := abs_siteSign x e.succ
      have hy1 := abs_siteSign y e.castSucc
      have hy2 := abs_siteSign y e.succ
      have h1 : |b * (siteSign x e.castSucc * siteSign x e.succ)| = b := by
        rw [abs_mul, abs_mul, hx1, hx2, abs_of_nonneg hb]
        ring
      have h2 : |b * (siteSign y e.castSucc * siteSign y e.succ)| = b := by
        rw [abs_mul, abs_mul, hy1, hy2, abs_of_nonneg hb]
        ring
      calc |b * (siteSign x e.castSucc * siteSign x e.succ)
            - b * (siteSign y e.castSucc * siteSign y e.succ)|
          ≤ |b * (siteSign x e.castSucc * siteSign x e.succ)|
            + |b * (siteSign y e.castSucc * siteSign y e.succ)| := abs_sub _ _
        _ = 2 * b := by rw [h1, h2]; ring
    refine le_trans (Finset.sum_le_sum hterm) (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  rw [pathDiagEnergy_sepCarrier, pathDiagEnergy_sepCarrier]
  have hsplit : ((∑ s : Fin (n + 2), A * 3 ^ (s : ℕ) * siteSign x s)
        + ∑ e : Fin (n + 1), b * (siteSign x e.castSucc * siteSign x e.succ))
      - ((∑ s : Fin (n + 2), A * 3 ^ (s : ℕ) * siteSign y s)
        + ∑ e : Fin (n + 1), b * (siteSign y e.castSucc * siteSign y e.succ))
      = ((∑ s : Fin (n + 2), A * 3 ^ (s : ℕ) * siteSign x s)
          - ∑ s : Fin (n + 2), A * 3 ^ (s : ℕ) * siteSign y s)
        + ((∑ e : Fin (n + 1), b * (siteSign x e.castSucc * siteSign x e.succ))
          - ∑ e : Fin (n + 1), b * (siteSign y e.castSucc * siteSign y e.succ)) := by ring
  rw [hsplit]
  have := abs_sub_abs_le_abs_sub
    ((∑ s : Fin (n + 2), A * 3 ^ (s : ℕ) * siteSign x s)
      - ∑ s : Fin (n + 2), A * 3 ^ (s : ℕ) * siteSign y s)
    (-((∑ e : Fin (n + 1), b * (siteSign x e.castSucc * siteSign x e.succ))
      - ∑ e : Fin (n + 1), b * (siteSign y e.castSucc * siteSign y e.succ)))
  rw [abs_neg, sub_neg_eq_add] at this
  linarith [this, honsite_ge, hedge]


/-- The classical energies are Lipschitz in the coefficient vector. -/
theorem abs_pathDiagEnergy_sub_le (u v : PathShell n)
    (x : FiniteQubitConfiguration (Fin (n + 2))) :
    |pathDiagEnergy u x - pathDiagEnergy v x| ≤ (2 * (n : ℝ) + 3) * ‖u - v‖ := by
  classical
  have hcoord : ∀ l : PathLabel n, |u l - v l| ≤ ‖u - v‖ := by
    intro l
    have := abs_coord_le_norm (u - v) l
    simpa using this
  have hdiff : pathDiagEnergy u x - pathDiagEnergy v x
      = (∑ s : Fin (n + 2), (u (Sum.inl (s, 2)) - v (Sum.inl (s, 2))) *
          zSetSign ({s} : Finset (Fin (n + 2))) x)
        + ∑ e : Fin (n + 1), (u (Sum.inr (e, (2, 2))) - v (Sum.inr (e, (2, 2)))) *
            zSetSign ({e.castSucc, e.succ} : Finset (Fin (n + 2))) x := by
    have h1 : (∑ s : Fin (n + 2), (u (Sum.inl (s, 2)) - v (Sum.inl (s, 2))) *
          zSetSign ({s} : Finset (Fin (n + 2))) x)
        = (∑ s : Fin (n + 2), u (Sum.inl (s, 2)) * zSetSign ({s} : Finset (Fin (n + 2))) x)
          - ∑ s : Fin (n + 2), v (Sum.inl (s, 2)) * zSetSign ({s} : Finset (Fin (n + 2))) x := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun s _ => by ring
    have h2 : (∑ e : Fin (n + 1), (u (Sum.inr (e, (2, 2))) - v (Sum.inr (e, (2, 2)))) *
          zSetSign ({e.castSucc, e.succ} : Finset (Fin (n + 2))) x)
        = (∑ e : Fin (n + 1), u (Sum.inr (e, (2, 2))) *
            zSetSign ({e.castSucc, e.succ} : Finset (Fin (n + 2))) x)
          - ∑ e : Fin (n + 1), v (Sum.inr (e, (2, 2))) *
            zSetSign ({e.castSucc, e.succ} : Finset (Fin (n + 2))) x := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun e _ => by ring
    rw [pathDiagEnergy, pathDiagEnergy, h1, h2]
    ring
  rw [hdiff]
  refine le_trans (abs_add_le _ _) ?_
  have hons : |∑ s : Fin (n + 2), (u (Sum.inl (s, 2)) - v (Sum.inl (s, 2))) *
      zSetSign ({s} : Finset (Fin (n + 2))) x| ≤ ((n : ℝ) + 2) * ‖u - v‖ := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hterm : ∀ s ∈ (Finset.univ : Finset (Fin (n + 2))),
        |(u (Sum.inl (s, 2)) - v (Sum.inl (s, 2))) *
          zSetSign ({s} : Finset (Fin (n + 2))) x| ≤ ‖u - v‖ := by
      intro s _
      rw [abs_mul, abs_zSetSign, mul_one]
      exact hcoord _
    refine le_trans (Finset.sum_le_sum hterm) (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  have hedg : |∑ e : Fin (n + 1), (u (Sum.inr (e, (2, 2))) - v (Sum.inr (e, (2, 2)))) *
      zSetSign ({e.castSucc, e.succ} : Finset (Fin (n + 2))) x| ≤ ((n : ℝ) + 1) * ‖u - v‖ := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hterm : ∀ e ∈ (Finset.univ : Finset (Fin (n + 1))),
        |(u (Sum.inr (e, (2, 2))) - v (Sum.inr (e, (2, 2)))) *
          zSetSign ({e.castSucc, e.succ} : Finset (Fin (n + 2))) x| ≤ ‖u - v‖ := by
      intro e _
      rw [abs_mul, abs_zSetSign, mul_one]
      exact hcoord _
    refine le_trans (Finset.sum_le_sum hterm) (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  nlinarith [hons, hedg, norm_nonneg (u - v)]

/-- **A uniform energy gap near the separating direction.**  Every carrier coefficient vector
within the stated radius of the base-three direction still separates the classical energies, by
half the original gap. -/
theorem gap_near_sepCarrier {A b rho : ℝ} (hA : 0 ≤ A) (hb : 0 ≤ b)
    {u : PathShell n} (hu : ‖u - sepCarrier n A b‖ ≤ rho)
    (hrho : (2 * (n : ℝ) + 3) * rho ≤ (2 * A - 2 * b * ((n : ℝ) + 1)) / 4)
    {x y : FiniteQubitConfiguration (Fin (n + 2))} (hxy : x ≠ y) :
    (2 * A - 2 * b * ((n : ℝ) + 1)) / 2 ≤ |pathDiagEnergy u x - pathDiagEnergy u y| := by
  have hbase := abs_sub_pathDiagEnergy_sepCarrier_ge (n := n) hA hb hxy
  have hx := abs_pathDiagEnergy_sub_le u (sepCarrier n A b) x
  have hy := abs_pathDiagEnergy_sub_le u (sepCarrier n A b) y
  have hnn : (0 : ℝ) ≤ 2 * (n : ℝ) + 3 := by positivity
  have hxle : |pathDiagEnergy u x - pathDiagEnergy (sepCarrier n A b) x|
      ≤ (2 * A - 2 * b * ((n : ℝ) + 1)) / 4 := by
    refine le_trans hx (le_trans (mul_le_mul_of_nonneg_left hu hnn) hrho)
  have hyle : |pathDiagEnergy u y - pathDiagEnergy (sepCarrier n A b) y|
      ≤ (2 * A - 2 * b * ((n : ℝ) + 1)) / 4 := by
    refine le_trans hy (le_trans (mul_le_mul_of_nonneg_left hu hnn) hrho)
  have habs1 := abs_le.mp hxle
  have habs2 := abs_le.mp hyle
  have hbaseabs := abs_le.mp (le_refl |pathDiagEnergy (sepCarrier n A b) x
    - pathDiagEnergy (sepCarrier n A b) y|)
  rcases abs_cases (pathDiagEnergy (sepCarrier n A b) x
      - pathDiagEnergy (sepCarrier n A b) y) with ⟨hc, -⟩ | ⟨hc, -⟩
  · rw [hc] at hbase
    refine le_trans ?_ (le_abs_self _)
    have hb1 := abs_le.mp (le_of_eq (rfl : |pathDiagEnergy u x - pathDiagEnergy (sepCarrier n A b) x|
      = |pathDiagEnergy u x - pathDiagEnergy (sepCarrier n A b) x|))
    linarith [habs1.1, habs1.2, habs2.1, habs2.2, hbase]
  · rw [hc] at hbase
    refine le_trans ?_ (neg_le_abs _)
    linarith [habs1.1, habs1.2, habs2.1, habs2.2, hbase]

end GaloisForLFunctions.HTGeometry

end
