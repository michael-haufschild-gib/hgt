import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.MaximalError.FieldDeficit
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.IsolatedFieldDensity
import GaloisForLFunctions.HTGeometry.Quantum.PhysicalCircuitInversion

/-! # Extensive physical gate cost up to every error strictly below two -/
open Matrix MeasureTheory Filter Real Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.MaximalError
noncomputable section

/-- Even an error arbitrarily close to two requires a positive density of
gates throughout each bounded horizon from inverse-size onset. -/
private theorem positive_window {ε T : ℝ} (hε : ε < 2) (hT : 0 ≤ T) :
    ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      ∀ t : ℝ, A ≤ (n+2:ℕ)*t → t ≤ T → ∀ s : ℕ,
        HasProjectiveCircuitApproximation (n+2) ε s
          (unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t) → c*(n+2:ℕ) < s := by
  classical
  let g := 2-ε
  have hg : 0 < g := sub_pos.mpr hε
  let q := g/(8*(T+1))
  have hq : 0 < q := div_pos hg (by positivity)
  let L := π/q+T
  have hL : 0 < L := add_pos_of_pos_of_nonneg (div_pos pi_pos hq) hT
  let δ := g/(84*L)
  have hδ : 0 < δ := div_pos hg (by positivity)
  obtain ⟨p,hp,h⟩ := gaussian_path_eventual_isolated_sites q δ hδ
  refine ⟨2*L/p,p/4,by positivity,by positivity,?_⟩
  filter_upwards [h] with ω hw
  filter_upwards [hw] with n hn
  obtain ⟨S,hsize,his⟩ := hn
  intro t hlate ht s hfit
  by_contra! hcost
  obtain ⟨b,hb,C,hC,herr⟩ := hfit
  let N := ((n+2:ℕ):ℝ)
  have hN : 0 < N := by dsimp [N]; positivity
  have hc : (C.gateCount:ℝ) ≤ p/4*N := (Nat.cast_le.mpr hC).trans hcost
  have ht₀ : 0 < t := pos_of_mul_pos_right ((show 0 < 2*L/p by positivity).trans_le hlate) hN.le
  let R := S \ C.touchedSites
  have hrem := card_sdiff_add_card_inter S C.touchedSites
  have hin := (card_le_card (inter_subset_right : S∩C.touchedSites ⊆ C.touchedSites)).trans C.card_touchedSites_le
  have hr : p/2*N ≤ (R.card:ℝ) := by
    have hr₁ : (R.card:ℝ)+((S∩C.touchedSites).card:ℝ)=(S.card:ℝ) := by exact_mod_cast hrem
    have hr₂ : ((S∩C.touchedSites).card:ℝ) ≤ 2*(C.gateCount:ℝ) := by exact_mod_cast hin
    linarith only [hc,hr₁,hr₂,hsize]
  let m := ⌈π/(t*q)⌉₊
  have htq := mul_pos ht₀ hq
  have hspan := (div_le_iff₀ htq).mp (Nat.le_ceil (π/(t*q)))
  have hm : (m:ℝ)*t ≤ L := by
    have h := (Nat.ceil_lt_add_one (div_nonneg pi_pos.le htq.le)).le
    have he : π/(t*q)*t=π/q := by field_simp [hq.ne',ht₀.ne']
    have hh := mul_le_mul_of_nonneg_right h ht₀.le
    rw [add_mul,he,one_mul] at hh
    exact hh.trans (add_le_add le_rfl ht)
  have hLr : L ≤ (R.card:ℝ)*t := by
    have he := (div_le_iff₀ hp).mp hlate
    nlinarith only [he,mul_le_mul_of_nonneg_right hr ht₀.le]
  have hmR : m ≤ R.card := Nat.cast_le.mp ((mul_le_mul_iff_left₀ ht₀).mp (hm.trans hLr))
  obtain ⟨J,hJ,hcard⟩ := exists_subset_card_eq hmR
  have hmem (i) (hi : i∈J) := mem_sdiff.mp (hJ hi : i∈S \ C.touchedSites)
  have hbad := packet_deficit (pathPauliDisorderShell ω n) J hq hδ.le ht₀
    (by rw [hcard,mul_comm (t*q)]; exact hspan) (fun i hi => his i (hmem i hi).1)
    C (disjoint_left.mpr fun i hi => (hmem i hi).2) b hb
  rw [hcard] at hbad
  have hqeq : q*(8*(T+1))=g := div_mul_cancel₀ _ (show 8*(T+1)≠0 by positivity)
  have hδeq : δ*(84*L)=g := div_mul_cancel₀ _ (show 84*L≠0 by positivity)
  change (m:ℝ)*t ≤ L at hm
  nlinarith only [hbad,herr,hqeq,hδeq,mul_le_mul_of_nonneg_left ht hq.le,
    mul_le_mul_of_nonneg_right hm hδ.le,hq,show g=2-ε from rfl,hg]

/-- At every fixed tolerance below the projective diameter, a physical
fit on either side of the identity needs a positive density of gates
from inverse-size onset through any bounded horizon. -/
theorem gaussian_positive_density_below_diameter {ε T : ℝ} (hε : ε < 2) (hT : 0 ≤ T) :
    ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      ∀ t : ℝ, A ≤ (n+2:ℕ)*|t| → |t| ≤ T → ∀ s : ℕ,
        HasProjectiveCircuitApproximation (n+2) ε s
          (unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t) → c*(n+2:ℕ) < s := by
  obtain ⟨A,c,hA,hc,h⟩ := positive_window hε hT
  refine ⟨A,c,hA,hc,?_⟩
  filter_upwards [h] with ω hw
  filter_upwards [hw] with n hn
  intro t hlo hhi s hf
  apply hn |t| hlo hhi s
  rcases le_total 0 t with ht|ht
  · simpa only [abs_of_nonneg ht] using hf
  · rw [abs_of_nonpos ht]
    exact HasProjectiveCircuitApproximation.neg_time
      ⟨pathHamiltonian (pathPauliDisorderShell ω n),isSelfAdjoint_pathHamiltonian _⟩ hf

#print axioms gaussian_positive_density_below_diameter
end
end GaloisForLFunctions.HTGeometry.MaximalError
