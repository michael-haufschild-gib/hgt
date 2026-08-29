import GaloisForLFunctions.HTGeometry.UnitaryPairTwistHardyBound
import GaloisForLFunctions.HTGeometry.UnimodularMulLp

open Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

/-- A quantitatively bounded family of invertible operators between two particle-number-indexed
Hardy subspaces. The ambient spaces already encode the analytic Hardy-domain regularity. -/
structure HardyIntertwinerFamily
    (E : ℕ → Type u) [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace ℂ (E n)]
    (source target : ∀ n, Submodule ℂ (E n)) where
  gamma : ℝ
  gammaInv : ℝ
  one_le_gamma : 1 ≤ gamma
  one_le_gammaInv : 1 ≤ gammaInv
  forward : ∀ n, E n →L[ℂ] E n
  inverse : ∀ n, E n →L[ℂ] E n
  forward_inverse : ∀ n, forward n * inverse n = 1
  inverse_forward : ∀ n, inverse n * forward n = 1
  maps_forward : ∀ n, MapsTo (forward n) (source n) (target n)
  maps_inverse : ∀ n, MapsTo (inverse n) (target n) (source n)
  norm_forward : ∀ n, ‖forward n‖ ≤ gamma ^ n
  norm_inverse : ∀ n, ‖inverse n‖ ≤ gammaInv ^ n

namespace HardyIntertwinerFamily

variable {E : ℕ → Type u} [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace ℂ (E n)]
  {source middle target : ∀ n, Submodule ℂ (E n)}

/-- Reverse a bounded Hardy intertwiner family, exchanging its two quantitative constants. -/
def symm (J : HardyIntertwinerFamily E source target) :
    HardyIntertwinerFamily E target source where
  gamma := J.gammaInv
  gammaInv := J.gamma
  one_le_gamma := J.one_le_gammaInv
  one_le_gammaInv := J.one_le_gamma
  forward := J.inverse
  inverse := J.forward
  forward_inverse := J.inverse_forward
  inverse_forward := J.forward_inverse
  maps_forward := J.maps_inverse
  maps_inverse := J.maps_forward
  norm_forward := J.norm_inverse
  norm_inverse := J.norm_forward

/-- Composition of Hardy intertwiner families. Exponential bases multiply in the exact order
forced by the forward and inverse compositions. -/
def comp (I : HardyIntertwinerFamily E middle target)
    (J : HardyIntertwinerFamily E source middle) :
    HardyIntertwinerFamily E source target where
  gamma := I.gamma * J.gamma
  gammaInv := J.gammaInv * I.gammaInv
  one_le_gamma := one_le_mul_of_one_le_of_one_le I.one_le_gamma J.one_le_gamma
  one_le_gammaInv := one_le_mul_of_one_le_of_one_le J.one_le_gammaInv I.one_le_gammaInv
  forward := fun n => I.forward n * J.forward n
  inverse := fun n => J.inverse n * I.inverse n
  forward_inverse := by
    intro n
    calc
      (I.forward n * J.forward n) * (J.inverse n * I.inverse n) =
          I.forward n * (J.forward n * J.inverse n) * I.inverse n := by
            noncomm_ring
      _ = I.forward n * 1 * I.inverse n := by rw [J.forward_inverse n]
      _ = 1 := by simpa using I.forward_inverse n
  inverse_forward := by
    intro n
    calc
      (J.inverse n * I.inverse n) * (I.forward n * J.forward n) =
          J.inverse n * (I.inverse n * I.forward n) * J.forward n := by
            noncomm_ring
      _ = J.inverse n * 1 * J.forward n := by rw [I.inverse_forward n]
      _ = 1 := by simpa using J.inverse_forward n
  maps_forward := by
    intro n x hx
    exact I.maps_forward n (J.maps_forward n hx)
  maps_inverse := by
    intro n x hx
    exact J.maps_inverse n (I.maps_inverse n hx)
  norm_forward := by
    intro n
    calc
      ‖I.forward n * J.forward n‖ ≤ ‖I.forward n‖ * ‖J.forward n‖ := norm_mul_le _ _
      _ ≤ I.gamma ^ n * J.gamma ^ n := mul_le_mul (I.norm_forward n) (J.norm_forward n)
          (norm_nonneg _) (pow_nonneg (le_trans zero_le_one I.one_le_gamma) _)
      _ = (I.gamma * J.gamma) ^ n := (mul_pow _ _ _).symm
  norm_inverse := by
    intro n
    calc
      ‖J.inverse n * I.inverse n‖ ≤ ‖J.inverse n‖ * ‖I.inverse n‖ := norm_mul_le _ _
      _ ≤ J.gammaInv ^ n * I.gammaInv ^ n :=
        mul_le_mul (J.norm_inverse n) (I.norm_inverse n) (norm_nonneg _)
          (pow_nonneg (le_trans zero_le_one J.one_le_gammaInv) _)
      _ = (J.gammaInv * I.gammaInv) ^ n := (mul_pow _ _ _).symm

end HardyIntertwinerFamily

/-- Existence of one all-particle Hardy intertwiner with uniform exponential constants. -/
def HasHardyIntertwiner
    (E : ℕ → Type u) [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace ℂ (E n)]
    (source target : ∀ n, Submodule ℂ (E n)) : Prop :=
  Nonempty (HardyIntertwinerFamily E source target)

/-- A bounded scalar CDD intertwiner transports the all-particle Hardy intertwiner property in
both directions. -/
theorem hasHardyIntertwiner_iff_of_scalarCDD
    {E : ℕ → Type u} [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace ℂ (E n)]
    {dressed base reference : ∀ n, Submodule ℂ (E n)}
    (J : HardyIntertwinerFamily E dressed base) :
    HasHardyIntertwiner E base reference ↔ HasHardyIntertwiner E dressed reference := by
  constructor
  · rintro ⟨I⟩
    exact ⟨I.comp J⟩
  · rintro ⟨I⟩
    exact ⟨I.comp J.symm⟩

section Exchange

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- Central scalar dressing of a matrix-valued two-body exchange factor. -/
def scalarCDD (phi : ℝ → ℂ) (B : ℝ → (V →L[ℂ] V)) (t : ℝ) : V →L[ℂ] V :=
  phi t • B t

/-- Adjacent-generator exchange law at fixed particle number. -/
def ObeysAdjacentExchange (B : ℝ → (V →L[ℂ] V))
    (psi : (ℕ → ℝ) → V) (m n : ℕ) : Prop :=
  m + 1 < n ∧ ∀ theta, psi (swapAt m theta) = B (theta m - theta (m + 1)) (psi theta)

/-- All adjacent-generator exchange laws. -/
def ObeysExchange (B : ℝ → (V →L[ℂ] V))
    (psi : (ℕ → ℝ) → V) (n : ℕ) : Prop :=
  ∀ m, m + 1 < n →
    ∀ theta, psi (swapAt m theta) = B (theta m - theta (m + 1)) (psi theta)

/-- Scalar pair multiplication of a vector-valued rapidity section. -/
def pairMultiplySection (y : ℝ → ℂ) (n : ℕ) (psi : (ℕ → ℝ) → V) :
    (ℕ → ℝ) → V :=
  fun theta => pairMultiplier y theta n • psi theta

/-- Equation (8): the concrete Lechner pair multiplier cancels an anchor-preserving scalar CDD
factor at every adjacent generator, including matrix-valued exchange factors. -/
theorem pairMultiplySection_obeysExchange_of_scalarCDD
    {phi y : ℝ → ℂ} {B : ℝ → (V →L[ℂ] V)}
    (hy : ∀ t, y t ≠ 0) (hphi : ∀ t, phi t = y t / y (-t))
    {psi : (ℕ → ℝ) → V} {n : ℕ}
    (hpsi : ObeysExchange (scalarCDD phi B) psi n) :
    ObeysExchange B (pairMultiplySection y n psi) n := by
  intro m hm theta
  let d : ℝ := theta m - theta (m + 1)
  have hrel := pairMultiplier_swapAt y theta (m := m) (n := n) hm
  have hneg : theta (m + 1) - theta m = -d := by simp [d]
  have hrel' : pairMultiplier y (swapAt m theta) n * y d =
      pairMultiplier y theta n * y (-d) := by
    simpa only [d, neg_sub] using hrel
  have hscalar : pairMultiplier y (swapAt m theta) n * phi d = pairMultiplier y theta n := by
    rw [hphi, div_eq_mul_inv, ← mul_assoc, hrel']
    simp [hy (-d)]
  rw [pairMultiplySection, hpsi m hm theta]
  simp only [scalarCDD, smul_apply, smul_smul]
  rw [hscalar]
  simp [pairMultiplySection]

/-- The concrete pair multiplier gives an equivalence of complete exchange spaces. Unimodularity
is used only to certify that the scalar multiplier can be cancelled pointwise. -/
theorem pairMultiplySection_obeysExchange_iff_scalarCDD
    {phi y : ℝ → ℂ} {B : ℝ → (V →L[ℂ] V)}
    (hy : ∀ t, ‖y t‖ = 1) (hphi : ∀ t, phi t = y t / y (-t))
    {psi : (ℕ → ℝ) → V} {n : ℕ} :
    ObeysExchange (scalarCDD phi B) psi n ↔
      ObeysExchange B (pairMultiplySection y n psi) n := by
  constructor
  · exact pairMultiplySection_obeysExchange_of_scalarCDD
      (fun t => norm_ne_zero_iff.mp (by rw [hy t]; norm_num)) hphi
  · intro htrans m hm theta
    let d : ℝ := theta m - theta (m + 1)
    let c : ℂ := pairMultiplier y (swapAt m theta) n
    have hc : c ≠ 0 := pairMultiplier_ne_zero hy (swapAt m theta) n
    have hrel := pairMultiplier_swapAt y theta (m := m) (n := n) hm
    have hrel' : c * y d = pairMultiplier y theta n * y (-d) := by
      simpa only [c, d, neg_sub] using hrel
    have hscalar : c * phi d = pairMultiplier y theta n := by
      rw [hphi, div_eq_mul_inv, ← mul_assoc, hrel']
      have hyneg : y (-d) ≠ 0 := norm_ne_zero_iff.mp (by rw [hy (-d)]; norm_num)
      simp [hyneg]
    have hexchange := htrans m hm theta
    have hcancel : c • psi (swapAt m theta) =
        c • (phi d • B d (psi theta)) := by
      calc
        c • psi (swapAt m theta) =
            B d (pairMultiplier y theta n • psi theta) := by
              simpa [pairMultiplySection, c, d] using hexchange
        _ = pairMultiplier y theta n • B d (psi theta) := by rw [map_smul]
        _ = (c * phi d) • B d (psi theta) := by rw [hscalar]
        _ = c • (phi d • B d (psi theta)) := by rw [mul_smul]
    have hcancelled := congrArg (fun v : V => c⁻¹ • v) hcancel
    simp only [smul_smul] at hcancelled
    rw [inv_mul_cancel₀ hc, one_smul, ← mul_assoc, inv_mul_cancel₀ hc, one_mul] at hcancelled
    simpa [scalarCDD, d] using hcancelled

/-- The scalar zero anchor leaves the matrix reference factor unchanged. -/
theorem scalarCDD_zero {phi : ℝ → ℂ} {B : ℝ → (V →L[ℂ] V)}
    (hphi0 : phi 0 = 1) : scalarCDD phi B 0 = B 0 := by
  simp [scalarCDD, hphi0]

end Exchange

section AnalyticPairMultiplier

/-- Holomorphic all-pair multiplier in finite complex rapidity coordinates, ordered exactly as
the real Lechner pair multiplier. -/
def analyticPairMultiplier (y : ℂ → ℂ) {n : ℕ} (zeta : Fin n → ℂ) : ℂ :=
  ∏ l : Fin n, ∏ k : Fin l, y (zeta (Fin.castLE l.isLt.le k) - zeta l)

/-- On real rapidities the analytic all-pair product is exactly `pairMultiplierFin`. -/
theorem analyticPairMultiplier_ofReal_eq_pairMultiplierFin
    (y : ℂ → ℂ) {n : ℕ} (theta : Fin n → ℝ) :
    analyticPairMultiplier y (fun i => theta i) =
      pairMultiplierFin (fun t => y t) theta := by
  rw [analyticPairMultiplier, pairMultiplierFin, pairMultiplier]
  simp only [Complex.ofReal_sub]
  rw [← Fin.prod_univ_eq_prod_range
    (fun l => ∏ k ∈ Finset.range l,
      y (embedFin theta k - embedFin theta l)) n]
  refine Finset.prod_congr rfl fun l hl => ?_
  rw [← Fin.prod_univ_eq_prod_range
    (fun k => y (embedFin theta k - embedFin theta l)) l]
  refine Finset.prod_congr rfl fun k hk => ?_
  have hkN : k.val < n := lt_trans k.isLt l.isLt
  rw [embedFin, dif_pos hkN, embedFin, dif_pos l.isLt]
  rfl

private theorem two_mul_choose_two_eq_mul_pred_scalarCDD (n : ℕ) :
    2 * n.choose 2 = n * (n - 1) := by
  rw [Nat.choose_two_right]
  refine Nat.mul_div_cancel' ?_
  rcases n with _ | m
  · simp
  · rw [Nat.succ_sub_one]
    have h := (Nat.even_mul_succ_self m).two_dvd
    rwa [mul_comm] at h

/-- Exact scalar specialization of the shrinking-tube pair-word theorem. The standard analytic
Lechner multiplier over all unordered pairs has an exponential-in-particle-number Hardy bound. -/
theorem norm_analyticPairMultiplier_le_hardyBase_pow
    {y : ℂ → ℂ} {n : ℕ} (hn : 0 < n)
    {kappa rho M : ℝ} (hkappa : 0 < kappa) (hrho : 0 < rho)
    (hkappaRho : kappa ≤ rho) (hM : 1 ≤ M)
    (hupper : DiffContOnHorizontalCl y 0 rho)
    (hlower : DiffContOnHorizontalCl y (-rho) 0)
    (hreal : ∀ x : ℝ, ‖y x‖ ≤ 1)
    (hstrip : ∀ z, |z.im| ≤ rho → ‖y z‖ ≤ M)
    {zeta : Fin n → ℂ} (hzeta : InShrinkingTube kappa zeta) :
    ‖analyticPairMultiplier y zeta‖ ≤ pairWordHardyBase M 1 kappa rho ^ n := by
  let e : ℝ := kappa / ((n : ℝ) * rho)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hkdiv : kappa / (n : ℝ) ≤ rho :=
    (div_le_self hkappa.le hnR).trans hkappaRho
  have heNonneg : 0 ≤ e := by positivity
  have hfactor : ∀ (l : Fin n) (k : Fin l),
      ‖y (zeta (Fin.castLE l.isLt.le k) - zeta l)‖ ≤ M ^ e := by
    intro l k
    let i : Fin n := Fin.castLE l.isLt.le k
    have him := (abs_im_sub_lt_of_mem_shrinkingTube hzeta i l).le
    have hthree := norm_le_rpow_abs_im_div_of_horizontal_threeLines
      hrho hM hupper hlower hreal hstrip (zeta i - zeta l) (him.trans hkdiv)
    exact hthree.trans (Real.rpow_le_rpow_of_exponent_le hM (by
      dsimp [e]
      calc
        |(zeta i - zeta l).im| / rho ≤ (kappa / (n : ℝ)) / rho :=
          div_le_div_of_nonneg_right him hrho.le
        _ = kappa / ((n : ℝ) * rho) := by rw [div_div]))
  have hinner : ∀ l : Fin n,
      ‖∏ k : Fin l, y (zeta (Fin.castLE l.isLt.le k) - zeta l)‖ ≤ (M ^ e) ^ l.val := by
    intro l
    rw [norm_prod]
    calc
      ∏ k : Fin l, ‖y (zeta (Fin.castLE l.isLt.le k) - zeta l)‖
          ≤ ∏ _k : Fin l, M ^ e :=
            Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun k _ => hfactor l k)
      _ = (M ^ e) ^ l.val := by simp
  rw [analyticPairMultiplier, norm_prod]
  calc
    ∏ l : Fin n, ‖∏ k : Fin l, y (zeta (Fin.castLE l.isLt.le k) - zeta l)‖
        ≤ ∏ l : Fin n, (M ^ e) ^ l.val :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun l _ => hinner l)
    _ = (M ^ e) ^ n.choose 2 := by
      rw [Finset.prod_pow_eq_pow_sum]
      congr 1
      calc
        ∑ i : Fin n, i.val = ∑ i ∈ Finset.range n, i :=
          Fin.sum_univ_eq_sum_range (fun i : ℕ => i) n
        _ = n * (n - 1) / 2 := Finset.sum_range_id n
        _ = n.choose 2 := (Nat.choose_two_right n).symm
    _ = M ^ (kappa * (n - 1 : ℕ) / (2 * rho)) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul (zero_le_one.trans hM)]
      congr 1
      dsimp [e]
      have hchoose : (2 : ℝ) * n.choose 2 = (n : ℝ) * (n - 1 : ℕ) := by
        exact_mod_cast two_mul_choose_two_eq_mul_pred_scalarCDD n
      field_simp
      nlinarith
    _ ≤ pairWordHardyBase M 1 kappa rho ^ n := by
      simpa using rpow_pairWordExponent_le_hardyBase_pow
        (n := n) (m := 1) hM hkappa hrho

/-- Products of pointwise inverse scalar factors are exact two-sided inverses at every complex
rapidity tuple. -/
theorem analyticPairMultiplier_twoSidedInverse
    {y g : ℂ → ℂ} (hyg : ∀ z, y z * g z = 1) (hgy : ∀ z, g z * y z = 1)
    {n : ℕ} (zeta : Fin n → ℂ) :
    analyticPairMultiplier y zeta * analyticPairMultiplier g zeta = 1 ∧
      analyticPairMultiplier g zeta * analyticPairMultiplier y zeta = 1 := by
  constructor <;>
    simp only [analyticPairMultiplier, ← Finset.prod_mul_distrib] <;>
    simp [hyg, hgy]

/-- Complete scalar pair-multiplier analytic certificate: exact two-sided inverse and exponential
Hardy bounds for multiplier and inverse on the same shrinking tube. -/
theorem scalarCDD_pairMultiplier_hardy_certificate
    {y g : ℂ → ℂ} {n : ℕ} (hn : 0 < n)
    {kappa rho M Mtilde : ℝ} (hkappa : 0 < kappa) (hrho : 0 < rho)
    (hkappaRho : kappa ≤ rho) (hM : 1 ≤ M) (hMtilde : 1 ≤ Mtilde)
    (hyg : ∀ z, y z * g z = 1) (hgy : ∀ z, g z * y z = 1)
    (hyupper : DiffContOnHorizontalCl y 0 rho)
    (hylower : DiffContOnHorizontalCl y (-rho) 0)
    (hyreal : ∀ x : ℝ, ‖y x‖ ≤ 1)
    (hystrip : ∀ z, |z.im| ≤ rho → ‖y z‖ ≤ M)
    (hgupper : DiffContOnHorizontalCl g 0 rho)
    (hglower : DiffContOnHorizontalCl g (-rho) 0)
    (hgreal : ∀ x : ℝ, ‖g x‖ ≤ 1)
    (hgstrip : ∀ z, |z.im| ≤ rho → ‖g z‖ ≤ Mtilde)
    {zeta : Fin n → ℂ} (hzeta : InShrinkingTube kappa zeta) :
    analyticPairMultiplier y zeta * analyticPairMultiplier g zeta = 1 ∧
      analyticPairMultiplier g zeta * analyticPairMultiplier y zeta = 1 ∧
      ‖analyticPairMultiplier y zeta‖ ≤ pairWordHardyBase M 1 kappa rho ^ n ∧
      ‖analyticPairMultiplier g zeta‖ ≤ pairWordHardyBase Mtilde 1 kappa rho ^ n := by
  obtain ⟨hright, hleft⟩ := analyticPairMultiplier_twoSidedInverse hyg hgy zeta
  exact ⟨hright, hleft,
    norm_analyticPairMultiplier_le_hardyBase_pow hn hkappa hrho hkappaRho hM
      hyupper hylower hyreal hystrip hzeta,
    norm_analyticPairMultiplier_le_hardyBase_pow hn hkappa hrho hkappaRho hMtilde
      hgupper hglower hgreal hgstrip hzeta⟩

/-- Common imaginary translation to the central Hardy boundary. -/
def centralRapidity {n : ℕ} (theta : Fin n → ℝ) : Fin n → ℂ :=
  fun i => theta i - Complex.I * (Real.pi / 2)

/-- The analytic multiplier's central boundary is exactly the real Lechner multiplier. -/
theorem analyticPairMultiplier_centralRapidity_eq_pairMultiplierFin
    (y : ℂ → ℂ) {n : ℕ} (theta : Fin n → ℝ) :
    analyticPairMultiplier y (centralRapidity theta) =
      pairMultiplierFin (fun t => y t) theta := by
  calc
    analyticPairMultiplier y (centralRapidity theta) =
        analyticPairMultiplier y (fun i => theta i) := by
          simp [analyticPairMultiplier, centralRapidity]
    _ = pairMultiplierFin (fun t => y t) theta :=
      analyticPairMultiplier_ofReal_eq_pairMultiplierFin y theta

/-- A unit-modulus half phase makes the analytic pair multiplier exactly unitary on the central
Hardy boundary. -/
theorem norm_analyticPairMultiplier_centralRapidity
    {y : ℂ → ℂ} (hy : ∀ t : ℝ, ‖y t‖ = 1)
    {n : ℕ} (theta : Fin n → ℝ) :
    ‖analyticPairMultiplier y (centralRapidity theta)‖ = 1 := by
  rw [analyticPairMultiplier_centralRapidity_eq_pairMultiplierFin]
  exact norm_pairMultiplierFin hy theta

end AnalyticPairMultiplier

end

end GaloisForLFunctions.HTGeometry
