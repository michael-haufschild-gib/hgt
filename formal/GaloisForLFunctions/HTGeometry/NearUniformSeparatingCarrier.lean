/-
# A near-uniform carrier direction with separated energies

The base-three direction separates the classical energies but makes the edge couplings
exponentially smaller than the onsite ones, so on the unit sphere it violates the strong-bond
condition.  Perturbing the *uniform* carrier by an exponentially small base-three profile keeps
every coordinate between one and two -- hence of order `n^{-1/2}` after normalization -- and still
separates the energies: the unperturbed part of an energy difference is an even integer, so it is
either zero, in which case the base-three part alone gives `2ε`, or at least two, in which case the
base-three part is too small to cancel it.

Main results:
* `nearUniformCarrier` — the perturbed uniform carrier direction.
* `nearUniformCarrier_coord_mem` — every carrier coordinate lies in `[1,2]`.
* `separation_nearUniformCarrier` — **the energies are separated by `2ε`**.
-/
import GaloisForLFunctions.HTGeometry.PathCarrierSeparatingDirection

open Matrix Finset
open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

/-- The integer sign of a bit. -/
def signZ (b : Bool) : ℤ := if b then -1 else 1

theorem siteSign_eq_signZ {m : ℕ} (x : Fin m → Bool) (s : Fin m) :
    siteSign x s = ((signZ (x s) : ℤ) : ℝ) := by
  by_cases h : x s <;> simp [siteSign, signZ, h]

theorem even_signZ_sub (a b : Bool) : Even (signZ a - signZ b) := by
  by_cases ha : a <;> by_cases hb : b <;> simp [signZ, ha, hb]

theorem even_signZ_mul_sub (a b c d : Bool) :
    Even (signZ a * signZ b - signZ c * signZ d) := by
  by_cases ha : a <;> by_cases hb : b <;> by_cases hc : c <;> by_cases hd : d <;>
    simp [signZ, ha, hb, hc, hd]

variable {n : ℕ}

/-- The uniform carrier direction perturbed by an `ε`-scaled base-three onsite profile. -/
def nearUniformCarrier (n : ℕ) (eps : ℝ) : PathShell n :=
  WithLp.toLp 2 fun l =>
    match l with
    | Sum.inl sq => if sq.2 = 2 then 1 + eps * 3 ^ (sq.1 : ℕ) else 0
    | Sum.inr eab => if eab.2 = (2, 2) then 1 else 0

theorem nearUniformCarrier_offDiag (eps : ℝ) (l : PathLabel n) (hl : ¬ IsDiagLabel l) :
    nearUniformCarrier n eps l = 0 := by
  cases l with
  | inl sq =>
      have : sq.2 ≠ 2 := by simpa [IsDiagLabel] using hl
      show (if sq.2 = 2 then 1 + eps * 3 ^ (sq.1 : ℕ) else 0) = 0
      rw [if_neg this]
  | inr eab =>
      have : eab.2 ≠ (2, 2) := by simpa [IsDiagLabel] using hl
      show (if eab.2 = (2, 2) then (1 : ℝ) else 0) = 0
      rw [if_neg this]

theorem nearUniformCarrier_onsite (eps : ℝ) (s : Fin (n + 2)) :
    nearUniformCarrier n eps (Sum.inl (s, 2)) = 1 + eps * 3 ^ (s : ℕ) := by
  show (if (2 : Fin 3) = 2 then 1 + eps * 3 ^ (s : ℕ) else 0) = _
  rw [if_pos rfl]

theorem nearUniformCarrier_edge (eps : ℝ) (e : Fin (n + 1)) :
    nearUniformCarrier n eps (Sum.inr (e, (2, 2))) = 1 := by
  show (if ((2 : Fin 3), (2 : Fin 3)) = (2, 2) then (1 : ℝ) else 0) = _
  rw [if_pos rfl]

/-- Every diagonal coordinate of the direction lies between one and two. -/
theorem nearUniformCarrier_coord_mem {eps : ℝ} (heps : 0 ≤ eps)
    (hsmall : eps * 3 ^ (n + 2) ≤ 1) (l : PathLabel n) (hl : IsDiagLabel l) :
    1 ≤ nearUniformCarrier n eps l ∧ nearUniformCarrier n eps l ≤ 2 := by
  cases l with
  | inl sq =>
      have hq : sq.2 = 2 := hl
      obtain ⟨s, q⟩ := sq
      simp only at hq
      subst hq
      rw [nearUniformCarrier_onsite]
      have hpow : (3 : ℝ) ^ (s : ℕ) ≤ 3 ^ (n + 2) :=
        pow_le_pow_right₀ (by norm_num) (le_of_lt s.isLt)
      constructor
      · nlinarith [heps, pow_pos (by norm_num : (0:ℝ) < 3) (s : ℕ)]
      · nlinarith [heps, hsmall, hpow]
  | inr eab =>
      have hab : eab.2 = (2, 2) := hl
      obtain ⟨e, ab⟩ := eab
      simp only at hab
      subst hab
      rw [nearUniformCarrier_edge]
      norm_num

theorem pathDiagEnergy_nearUniformCarrier (eps : ℝ)
    (x : FiniteQubitConfiguration (Fin (n + 2))) :
    pathDiagEnergy (nearUniformCarrier n eps) x
      = (∑ s : Fin (n + 2), (1 + eps * 3 ^ (s : ℕ)) * siteSign x s)
        + ∑ e : Fin (n + 1), siteSign x e.castSucc * siteSign x e.succ := by
  rw [pathDiagEnergy]
  congr 1
  · exact Finset.sum_congr rfl fun s _ => by
      rw [nearUniformCarrier_onsite, zSetSign_singleton_eq]
  · exact Finset.sum_congr rfl fun e _ => by
      rw [nearUniformCarrier_edge, zSetSign_pair_eq, one_mul]

/-- The integer part of an energy difference. -/
def energyIntDiff (x y : FiniteQubitConfiguration (Fin (n + 2))) : ℤ :=
  (∑ s : Fin (n + 2), (signZ (x s) - signZ (y s)))
    + ∑ e : Fin (n + 1), (signZ (x e.castSucc) * signZ (x e.succ)
        - signZ (y e.castSucc) * signZ (y e.succ))

theorem even_energyIntDiff (x y : FiniteQubitConfiguration (Fin (n + 2))) :
    Even (energyIntDiff x y) := by
  refine Even.add (Finset.even_sum _ fun s _ => even_signZ_sub _ _)
    (Finset.even_sum _ fun e _ => even_signZ_mul_sub _ _ _ _)

theorem pathDiagEnergy_sub_eq (eps : ℝ) (x y : FiniteQubitConfiguration (Fin (n + 2))) :
    pathDiagEnergy (nearUniformCarrier n eps) x - pathDiagEnergy (nearUniformCarrier n eps) y
      = ((energyIntDiff x y : ℤ) : ℝ)
        + eps * ∑ s : Fin (n + 2), (3 : ℝ) ^ (s : ℕ) * (siteSign x s - siteSign y s) := by
  rw [pathDiagEnergy_nearUniformCarrier, pathDiagEnergy_nearUniformCarrier, energyIntDiff]
  push_cast
  have h1 : (∑ s : Fin (n + 2), (1 + eps * 3 ^ (s : ℕ)) * siteSign x s)
        - ∑ s : Fin (n + 2), (1 + eps * 3 ^ (s : ℕ)) * siteSign y s
      = (∑ s : Fin (n + 2), ((signZ (x s) : ℝ) - (signZ (y s) : ℝ)))
        + eps * ∑ s : Fin (n + 2), (3 : ℝ) ^ (s : ℕ) * (siteSign x s - siteSign y s) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [siteSign_eq_signZ x s, siteSign_eq_signZ y s]
    ring
  have h2 : (∑ e : Fin (n + 1), siteSign x e.castSucc * siteSign x e.succ)
        - ∑ e : Fin (n + 1), siteSign y e.castSucc * siteSign y e.succ
      = ∑ e : Fin (n + 1), ((signZ (x e.castSucc) : ℝ) * (signZ (x e.succ) : ℝ)
          - (signZ (y e.castSucc) : ℝ) * (signZ (y e.succ) : ℝ)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [siteSign_eq_signZ x e.castSucc, siteSign_eq_signZ x e.succ,
      siteSign_eq_signZ y e.castSucc, siteSign_eq_signZ y e.succ]
  linarith [h1, h2]

/-- **The near-uniform carrier separates the energies.**  The unperturbed part of an energy
difference is an even integer: if it vanishes the base-three part alone gives `2ε`, and otherwise it
is at least two while the base-three part is below `2/3`. -/
theorem separation_nearUniformCarrier {eps : ℝ} (heps : 0 < eps)
    (hsmall : eps * 3 ^ (n + 2) ≤ 2 / 3)
    {x y : FiniteQubitConfiguration (Fin (n + 2))} (hxy : x ≠ y) :
    2 * eps ≤ |pathDiagEnergy (nearUniformCarrier n eps) x
      - pathDiagEnergy (nearUniformCarrier n eps) y| := by
  classical
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ,
    K = ∑ s : Fin (n + 2), (3 : ℝ) ^ (s : ℕ) * (siteSign x s - siteSign y s) := ⟨_, rfl⟩
  have hK2 : 2 ≤ |K| := by rw [hKdef]; exact two_le_abs_sum_signDiff hxy
  have hKle : |K| ≤ 3 ^ (n + 2) - 1 := by
    rw [hKdef]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hterm : ∀ s ∈ (Finset.univ : Finset (Fin (n + 2))),
        |(3 : ℝ) ^ (s : ℕ) * (siteSign x s - siteSign y s)| ≤ 2 * 3 ^ (s : ℕ) := by
      intro s _
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (3:ℝ) ^ (s : ℕ))]
      have := abs_siteSign_sub_le x y s
      nlinarith [pow_pos (by norm_num : (0:ℝ) < 3) (s : ℕ)]
    refine le_trans (Finset.sum_le_sum hterm) (le_of_eq ?_)
    have hval : ∑ s : Fin (n + 2), (2 : ℝ) * 3 ^ (s : ℕ)
        = ∑ j ∈ Finset.range (n + 2), (2 : ℝ) * 3 ^ j := by
      rw [Finset.sum_range fun j => (2 : ℝ) * 3 ^ j]
    rw [hval, sum_lt_three_pow]
  have hsplit := pathDiagEnergy_sub_eq (n := n) eps x y
  rw [← hKdef] at hsplit
  rcases eq_or_ne (energyIntDiff x y) 0 with hz | hz
  · rw [hsplit, hz]
    push_cast
    rw [zero_add, abs_mul, abs_of_pos heps]
    nlinarith [hK2, heps]
  · have heven := even_energyIntDiff x y
    have habs2 : (2 : ℤ) ≤ |energyIntDiff x y| := by
      obtain ⟨t, ht⟩ := heven
      have htne : t ≠ 0 := by
        intro h
        rw [h] at ht
        exact hz (by omega)
      have h1t : 1 ≤ |t| := by
        have := abs_pos.mpr htne
        omega
      have hgt : |energyIntDiff x y| = 2 * |t| := by
        rw [ht, show t + t = 2 * t by ring, abs_mul]
        norm_num
      omega
    have habs2R : (2 : ℝ) ≤ |((energyIntDiff x y : ℤ) : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast habs2
    have hepsK : |eps * K| ≤ 2 / 3 := by
      rw [abs_mul, abs_of_pos heps]
      have hpos : (0 : ℝ) < 3 ^ (n + 2) := by positivity
      nlinarith [hKle, heps.le, hsmall, abs_nonneg K]
    have hsmalleps : 2 * eps ≤ 2 / 3 := by
      have hone : (1 : ℝ) ≤ 3 ^ (n + 2) := one_le_pow₀ (by norm_num)
      nlinarith [hsmall, heps.le]
    rw [hsplit]
    have htri := abs_sub_abs_le_abs_sub (((energyIntDiff x y : ℤ) : ℝ)) (-(eps * K))
    rw [abs_neg, sub_neg_eq_add] at htri
    linarith [htri, habs2R, hepsK, hsmalleps]


/-! ## The normalized direction -/

theorem pathDiagEnergy_smul (c : ℝ) (u : PathShell n)
    (x : FiniteQubitConfiguration (Fin (n + 2))) :
    pathDiagEnergy (c • u) x = c * pathDiagEnergy u x := by
  simp only [pathDiagEnergy, mul_add, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun s _ => by
      show (c * WithLp.ofLp u (Sum.inl (s, 2))) * _ = c * (_ * _)
      ring
  · exact Finset.sum_congr rfl fun e _ => by
      show (c * WithLp.ofLp u (Sum.inr (e, (2, 2)))) * _ = c * (_ * _)
      ring

theorem sq_norm_nearUniformCarrier_mem {eps : ℝ} (heps : 0 ≤ eps)
    (hsmall : eps * 3 ^ (n + 2) ≤ 1) :
    ((2 * n + 3 : ℕ) : ℝ) ≤ ‖nearUniformCarrier n eps‖ ^ (2 : ℕ) ∧
      ‖nearUniformCarrier n eps‖ ^ (2 : ℕ) ≤ 4 * ((2 * n + 3 : ℕ) : ℝ) := by
  classical
  have hsq : ‖nearUniformCarrier n eps‖ ^ (2 : ℕ)
      = ∑ l : PathLabel n, (nearUniformCarrier n eps l) ^ (2 : ℕ) := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    exact Finset.sum_congr rfl fun l _ => by rw [Real.norm_eq_abs, sq_abs]
  have hfilter : ∑ l : PathLabel n, (nearUniformCarrier n eps l) ^ (2 : ℕ)
      = ∑ l ∈ Finset.univ.filter (IsDiagLabel (n := n)), (nearUniformCarrier n eps l) ^ (2 : ℕ) := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) fun l _ hl => ?_).symm
    have : ¬ IsDiagLabel l := by simpa using hl
    rw [nearUniformCarrier_offDiag eps l this]
    ring
  have hcard : (Finset.univ.filter (IsDiagLabel (n := n))).card = 2 * n + 3 := by
    rw [← card_diagLabel n, Fintype.card_subtype]
  constructor
  · rw [hsq, hfilter]
    have hterm : ∀ l ∈ Finset.univ.filter (IsDiagLabel (n := n)),
        (1 : ℝ) ≤ (nearUniformCarrier n eps l) ^ (2 : ℕ) := by
      intro l hl
      have hdiag : IsDiagLabel l := by simpa using hl
      obtain ⟨h1, -⟩ := nearUniformCarrier_coord_mem heps hsmall l hdiag
      nlinarith [h1]
    refine le_trans (le_of_eq ?_) (Finset.card_nsmul_le_sum _ _ 1 hterm)
    rw [hcard, nsmul_eq_mul, mul_one]
  · rw [hsq, hfilter]
    have hterm : ∀ l ∈ Finset.univ.filter (IsDiagLabel (n := n)),
        (nearUniformCarrier n eps l) ^ (2 : ℕ) ≤ 4 := by
      intro l hl
      have hdiag : IsDiagLabel l := by simpa using hl
      obtain ⟨h1, h2⟩ := nearUniformCarrier_coord_mem heps hsmall l hdiag
      nlinarith [h1, h2]
    refine le_trans (Finset.sum_le_card_nsmul _ _ 4 hterm) (le_of_eq ?_)
    rw [hcard, nsmul_eq_mul]
    ring

theorem norm_nearUniformCarrier_pos {eps : ℝ} (heps : 0 ≤ eps)
    (hsmall : eps * 3 ^ (n + 2) ≤ 1) : 0 < ‖nearUniformCarrier n eps‖ := by
  obtain ⟨hlow, -⟩ := sq_norm_nearUniformCarrier_mem heps hsmall
  have hpos : (0 : ℝ) < ((2 * n + 3 : ℕ) : ℝ) := by positivity
  nlinarith [norm_nonneg (nearUniformCarrier n eps), hlow, hpos]

theorem norm_nearUniformCarrier_le {eps : ℝ} (heps : 0 ≤ eps)
    (hsmall : eps * 3 ^ (n + 2) ≤ 1) :
    ‖nearUniformCarrier n eps‖ ≤ 2 * Real.sqrt ((2 * n + 3 : ℕ) : ℝ) := by
  obtain ⟨-, hhigh⟩ := sq_norm_nearUniformCarrier_mem heps hsmall
  have hnn : (0 : ℝ) ≤ 2 * Real.sqrt ((2 * n + 3 : ℕ) : ℝ) := by positivity
  refine le_of_pow_le_pow_left₀ (n := 2) (by norm_num) hnn ?_
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  linarith [hhigh]

/-- The normalized near-uniform carrier direction. -/
def nearUniformDir (n : ℕ) (eps : ℝ) : PathShell n :=
  ‖nearUniformCarrier n eps‖⁻¹ • nearUniformCarrier n eps

theorem norm_nearUniformDir {eps : ℝ} (heps : 0 ≤ eps) (hsmall : eps * 3 ^ (n + 2) ≤ 1) :
    ‖nearUniformDir n eps‖ = 1 := by
  have hpos := norm_nearUniformCarrier_pos heps hsmall
  rw [nearUniformDir, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_nonneg hpos.le,
    inv_mul_cancel₀ hpos.ne']

theorem nearUniformDir_offDiag {eps : ℝ} (l : PathLabel n) (hl : ¬ IsDiagLabel l) :
    nearUniformDir n eps l = 0 := by
  show ‖nearUniformCarrier n eps‖⁻¹ * nearUniformCarrier n eps l = 0
  rw [nearUniformCarrier_offDiag eps l hl, mul_zero]

/-- Every diagonal coordinate of the normalized direction is at least `1/(2√(2n+3))`. -/
theorem nearUniformDir_coord_ge {eps : ℝ} (heps : 0 ≤ eps) (hsmall : eps * 3 ^ (n + 2) ≤ 1)
    (l : PathLabel n) (hl : IsDiagLabel l) :
    (2 * Real.sqrt ((2 * n + 3 : ℕ) : ℝ))⁻¹ ≤ nearUniformDir n eps l := by
  obtain ⟨h1, -⟩ := nearUniformCarrier_coord_mem heps hsmall l hl
  have hpos := norm_nearUniformCarrier_pos heps hsmall
  have hle := norm_nearUniformCarrier_le heps hsmall
  have hsq : (0 : ℝ) < 2 * Real.sqrt ((2 * n + 3 : ℕ) : ℝ) := lt_of_lt_of_le hpos hle
  show (2 * Real.sqrt ((2 * n + 3 : ℕ) : ℝ))⁻¹
    ≤ ‖nearUniformCarrier n eps‖⁻¹ * nearUniformCarrier n eps l
  have hstep : ‖nearUniformCarrier n eps‖⁻¹ * 1
      ≤ ‖nearUniformCarrier n eps‖⁻¹ * nearUniformCarrier n eps l :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  refine le_trans ?_ hstep
  rw [mul_one]
  exact inv_anti₀ hpos hle

/-- **The normalized direction still separates the energies**, by `ε/√(2n+3)`. -/
theorem separation_nearUniformDir {eps : ℝ} (heps : 0 < eps)
    (hsmall : eps * 3 ^ (n + 2) ≤ 2 / 3)
    {x y : FiniteQubitConfiguration (Fin (n + 2))} (hxy : x ≠ y) :
    eps / Real.sqrt ((2 * n + 3 : ℕ) : ℝ)
      ≤ |pathDiagEnergy (nearUniformDir n eps) x - pathDiagEnergy (nearUniformDir n eps) y| := by
  have hone : (1 : ℝ) ≤ 3 ^ (n + 2) := one_le_pow₀ (by norm_num)
  have hsmall' : eps * 3 ^ (n + 2) ≤ 1 := by linarith
  have hpos := norm_nearUniformCarrier_pos heps.le hsmall'
  have hle := norm_nearUniformCarrier_le heps.le hsmall'
  have hbase := separation_nearUniformCarrier heps hsmall hxy
  rw [nearUniformDir, pathDiagEnergy_smul, pathDiagEnergy_smul, ← mul_sub, abs_mul,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖nearUniformCarrier n eps‖⁻¹)]
  have hsqrtpos : (0 : ℝ) < Real.sqrt ((2 * n + 3 : ℕ) : ℝ) := by
    refine Real.sqrt_pos.mpr ?_
    positivity
  rw [div_le_iff₀ hsqrtpos]
  have hinv : ‖nearUniformCarrier n eps‖⁻¹ * (2 * eps) ≤ ‖nearUniformCarrier n eps‖⁻¹ *
      |pathDiagEnergy (nearUniformCarrier n eps) x
        - pathDiagEnergy (nearUniformCarrier n eps) y| :=
    mul_le_mul_of_nonneg_left hbase (by positivity)
  have hkey : eps ≤ ‖nearUniformCarrier n eps‖⁻¹ * (2 * eps) * Real.sqrt ((2 * n + 3 : ℕ) : ℝ) := by
    rw [inv_mul_eq_div, div_mul_eq_mul_div, le_div_iff₀ hpos]
    nlinarith [hle, heps.le, hsqrtpos.le]
  nlinarith [hinv, hkey, hsqrtpos.le, mul_nonneg (le_of_lt (inv_pos.mpr hpos)) (abs_nonneg
    (pathDiagEnergy (nearUniformCarrier n eps) x - pathDiagEnergy (nearUniformCarrier n eps) y))]


/-- **Separation is stable.**  A gap at one coefficient vector survives to half its size on a ball
of radius `g/(4(2n+3))`. -/
theorem gap_near_of_gap {u v : PathShell n} {g rho : ℝ}
    (hbase : ∀ x y : FiniteQubitConfiguration (Fin (n + 2)), x ≠ y →
      g ≤ |pathDiagEnergy v x - pathDiagEnergy v y|)
    (hu : ‖u - v‖ ≤ rho) (hrho : (2 * (n : ℝ) + 3) * rho ≤ g / 4)
    {x y : FiniteQubitConfiguration (Fin (n + 2))} (hxy : x ≠ y) :
    g / 2 ≤ |pathDiagEnergy u x - pathDiagEnergy u y| := by
  have hnn : (0 : ℝ) ≤ 2 * (n : ℝ) + 3 := by positivity
  have hx := le_trans (abs_pathDiagEnergy_sub_le u v x)
    (le_trans (mul_le_mul_of_nonneg_left hu hnn) hrho)
  have hy := le_trans (abs_pathDiagEnergy_sub_le u v y)
    (le_trans (mul_le_mul_of_nonneg_left hu hnn) hrho)
  have hb := hbase x y hxy
  have habs1 := abs_le.mp hx
  have habs2 := abs_le.mp hy
  rcases abs_cases (pathDiagEnergy v x - pathDiagEnergy v y) with ⟨hc, -⟩ | ⟨hc, -⟩
  · rw [hc] at hb
    refine le_trans ?_ (le_abs_self _)
    linarith [habs1.1, habs1.2, habs2.1, habs2.2, hb]
  · rw [hc] at hb
    refine le_trans ?_ (neg_le_abs _)
    linarith [habs1.1, habs1.2, habs2.1, habs2.2, hb]

/-- **A uniform energy gap on a ball around the normalized near-uniform direction.** -/
theorem gap_near_nearUniformDir {eps rho : ℝ} (heps : 0 < eps)
    (hsmall : eps * 3 ^ (n + 2) ≤ 2 / 3)
    {u : PathShell n} (hu : ‖u - nearUniformDir n eps‖ ≤ rho)
    (hrho : (2 * (n : ℝ) + 3) * rho ≤ eps / (4 * Real.sqrt ((2 * n + 3 : ℕ) : ℝ)))
    {x y : FiniteQubitConfiguration (Fin (n + 2))} (hxy : x ≠ y) :
    eps / (2 * Real.sqrt ((2 * n + 3 : ℕ) : ℝ))
      ≤ |pathDiagEnergy u x - pathDiagEnergy u y| := by
  have hsqrtpos : (0 : ℝ) < Real.sqrt ((2 * n + 3 : ℕ) : ℝ) := by
    refine Real.sqrt_pos.mpr ?_
    positivity
  have hrho' : (2 * (n : ℝ) + 3) * rho
      ≤ (eps / Real.sqrt ((2 * n + 3 : ℕ) : ℝ)) / 4 := by
    refine le_trans hrho (le_of_eq ?_)
    field_simp
  have := gap_near_of_gap
    (v := nearUniformDir n eps) (g := eps / Real.sqrt ((2 * n + 3 : ℕ) : ℝ))
    (fun x y hxy => separation_nearUniformDir heps hsmall hxy) hu hrho' hxy
  refine le_trans (le_of_eq ?_) this
  field_simp

end GaloisForLFunctions.HTGeometry

end
