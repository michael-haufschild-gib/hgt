import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.Bulk.BlockApproximation.DisjointPackets
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.Bulk.BlockApproximation.PeriodicCuts
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.Bulk.PhaseStability

/-! # Quantitative trace estimate from deleting periodic bonds -/
open Finset Matrix Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.Bulk.PeriodicCuts
noncomputable section
variable {n : ℕ}

/-- Squared coefficient mass lost at the cuts. -/
def seamMass (L : ℕ) (u : PathShell n) := ∑ l ∈ labels L none, (u l)^2

theorem seamMass_nonneg (L : ℕ) (u : PathShell n) : 0 ≤ seamMass L u := sum_nonneg fun _ _ => sq_nonneg _

private def retained (L : ℕ) (u : PathShell n) : PathShell n := ∑ b, piece L u b

private theorem retained_apply (L : ℕ) (u : PathShell n) (l : PathLabel n) :
    retained L u l=if owner L l=none then 0 else u l := by
  change (∑ b, piece L u b).ofLp l=_
  rw [WithLp.ofLp_sum,Finset.sum_apply]
  cases he : owner L l with
  | none => simp [piece,he]
  | some b => simp [piece,he]

private theorem deleted_energy (L : ℕ) (u : PathShell n) :
    (∑ l : PathLabel n, (u l-retained L u l)^2)=seamMass L u := by
  rw [seamMass,labels,sum_filter]
  apply sum_congr rfl
  intro l _
  rw [retained_apply]
  split <;> simp

private theorem variance_split (L : ℕ) (u : PathShell n) :
    (∑ b, shellVariance (piece L u b))+seamMass L u=shellVariance u := by
  simp only [shellVariance,seamMass,labels,sum_filter]
  rw [sum_comm,←sum_add_distrib]
  apply sum_congr rfl
  intro l _
  cases h : owner L l with
  | none => simp [piece,h]
  | some b => simp [piece,h]

private theorem packet_norm {L : ℕ} (hL : 0<L) (u : PathShell n) {M : ℝ} (hM : 0≤M)
    (hu : ∀ l, |u l|≤M) (b : Fin (n+2)) : ‖pathHamiltonian (piece L u b)‖ ≤ 12*L*M := by
  rw [pathHamiltonian_eq_sum]
  apply (norm_sum_le _ _).trans
  have hterm (l : PathLabel n) : ‖((piece L u b l:ℝ):ℂ) • finitePauliMatrix (pathWord l)‖=
      if owner L l=some b then |u l| else 0 := by
    rw [norm_smul,norm_finitePauliMatrix,Complex.norm_real,Real.norm_eq_abs,mul_one]
    by_cases h : owner L l=some b <;> simp [piece,h]
  simp only [hterm,←sum_filter]
  calc (∑ l ∈ labels L (some b), |u l|) ≤ ∑ _l ∈ labels L (some b), M := sum_le_sum fun l _ => hu l
       _ ≤ _ := by
         rw [sum_const,nsmul_eq_mul]
         exact mul_le_mul_of_nonneg_right (by exact_mod_cast block_card hL b) hM

/-- With an extensive fourth coefficient moment, the share of variance
removed at periodic cuts tends to zero as their spacing increases. -/
theorem seam_mass_sq (L : ℕ) (u : PathShell n) :
    (seamMass L u)^2 ≤ 12*((n+2)/L+1:ℕ)*(∑ l : PathLabel n, |u l|^4) := by
  let S := labels (n:=n) L none
  have h := sq_sum_le_card_mul_sum_sq (s:=S) (f:=fun l => (u l)^2)
  have he (l : PathLabel n) : ((u l)^2)^2=|u l|^4 := by
    rw [show (4:ℕ)=2*2 by decide,pow_mul,sq_abs]
  simp only [he] at h
  exact h.trans (mul_le_mul (by exact_mod_cast seam_card (n:=n) L)
    (sum_le_sum_of_subset_of_nonneg (subset_univ S) fun _ _ _ => by positivity)
    (sum_nonneg fun _ _ => by positivity) (by positivity))

private theorem gauss_variance_step {a b : ℝ} (ha : 0≤a) (hb : 0≤b) :
    ‖(exp (-a):ℂ)-(exp (-(a+b)):ℂ)‖ ≤ b := by
  rw [neg_add,exp_add,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
    ←mul_one_sub,abs_mul,abs_of_pos (exp_pos _),abs_of_nonneg (sub_nonneg.mpr (exp_le_one_iff.mpr (neg_nonpos.mpr hb)))]
  have h := add_one_le_exp (-b)
  apply (mul_le_of_le_one_left (sub_nonneg.mpr (exp_le_one_iff.mpr (neg_nonpos.mpr hb)))
    (exp_le_one_iff.mpr (neg_nonpos.mpr ha))).trans
  linarith only [h]

/-- Deleting the seams changes the characteristic function by at most
|t|√e, where e is their variance. The surviving blocks cost at most
36 L M |t|³ v in total Gaussian comparison error. -/
theorem periodic_gaussian_error {L : ℕ} (hL : 0<L) (u : PathShell n) {M : ℝ} (hM : 0≤M)
    (hu : ∀ l, |u l|≤M) (t : ℝ) :
    let v := shellVariance u
    let e := seamMass L u
    ‖shellTrace u t-(exp (-(t^2*v/2)):ℂ)‖ ≤ |t| *sqrt e+36* |t|^3*L*M*v+t^2*e/2 := by
  intro v e
  let w := retained L u
  let q := ∑ b, shellVariance (piece L u b)
  have he : 0≤e := seamMass_nonneg L u
  have hq : 0≤q := sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _
  have hsplit : q+e=v := variance_split L u
  have h₁ : ‖shellTrace u t-shellTrace w t‖ ≤ |t| *sqrt e := by
    have h := path_characteristic_stability u w t
    rw [show (∑ l : PathLabel n, (u l-w l)^2)=e from deleted_energy L u] at h
    rw [shellTrace,shellTrace,←mul_sub,norm_mul,norm_inv,Complex.norm_natCast,
      ←div_eq_inv_mul,div_le_iff₀ (Nat.cast_pos.mpr Fintype.card_pos)]
    simp only [Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat]
    exact h.trans_eq (by ring)
  have h₂ := disjoint_shell_comparison (sites (n:=n) L) (piece L u) (disjoint_sites L) (piece_supported L u) t
  have hmass : (∑ b, ‖pathHamiltonian (piece L u b)‖*shellVariance (piece L u b)) ≤ 12*L*M*q := by
    dsimp only [q]
    rw [mul_sum]
    exact sum_le_sum fun b _ => mul_le_mul_of_nonneg_right (packet_norm hL u hM hu b)
      (sum_nonneg fun _ _ => sq_nonneg _)
  have hqv : q≤v := by linarith only [hsplit,he]
  have h₂' : ‖shellTrace w t-(exp (-(t^2*q/2)):ℂ)‖ ≤ 36* |t|^3*L*M*v := by
    apply h₂.trans
    exact ((mul_le_mul_of_nonneg_left hmass (by positivity)).trans
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hqv (by positivity)) (by positivity))).trans_eq (by ring)
  have h₃ := gauss_variance_step (a:=t^2*q/2) (b:=t^2*e/2) (div_nonneg (mul_nonneg (sq_nonneg t) hq) (by norm_num))
    (div_nonneg (mul_nonneg (sq_nonneg t) he) (by norm_num))
  rw [show t^2*q/2+t^2*e/2=t^2*v/2 by rw [←hsplit]; ring] at h₃
  exact (norm_sub_le_norm_sub_add_norm_sub _ (shellTrace w t) _).trans
    ((add_le_add h₁ ((norm_sub_le_norm_sub_add_norm_sub _ (exp (-(t^2*q/2)):ℂ) _).trans
      (add_le_add h₂' h₃))).trans_eq (by ring))

#print axioms seam_mass_sq
#print axioms periodic_gaussian_error
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.Bulk.PeriodicCuts
