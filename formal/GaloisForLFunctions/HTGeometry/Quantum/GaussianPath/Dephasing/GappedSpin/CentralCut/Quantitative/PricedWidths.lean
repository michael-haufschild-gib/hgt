import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.Quantitative.TransverseWidths
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.Quantitative.Prefactor
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.Incident
import GaloisForLFunctions.HTGeometry.PathShellPatchTransport

/-! # Dimension-uniform mass of a separated central-spin box -/
open MeasureTheory ProbabilityTheory Set Real
namespace GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
noncomputable section

/-- The bulk coordinates keep a width of order β/(M 3ᴷ). Shrinking
the fourteen transverse coordinates by √T costs a further factor T⁷. -/
theorem priced_transverse_widths {β : ℝ} (hβ : β ∈ Ioc (0:ℝ) (1/2)) :
    ∃ C > (0:ℝ), ∀ {n : ℕ} (a b : Fin (n+1)) (w : PathShell n),
      let K := n+2
      let M := Fintype.card (PathLabel n)
      let r := β/((M:ℝ)*3^K)/2
      (∀ l, ¬IsDiagLabel l → w l=0) →
      (∀ l : PathLabel n, |w l| ≤ 2+(if l=.inl (a.succ,2) then 2*(M:ℝ)+3 else 0)) →
      ∀ T ≥ (1:ℝ), ∃ E : Set (PathLabel n→ℝ), MeasurableSet E ∧
        exp (-C*(K:ℝ)^2) ≤ T^7*(Measure.pi (fun _ : PathLabel n => gaussianReal 0 1)).real E ∧
        ∀ x∈E, (∀ l, |x l-w l| ≤ r) ∧
          ∀ l∈transverseLabels a b, |x l| ≤ r/(1800*sqrt T) := by
  classical
  let f := (sqrt (2*π))⁻¹
  have hf : 0 < f := by dsimp only [f]; positivity
  obtain ⟨C,hC,hprice⟩ := quadratic_box_prefactor (mul_pos hf hβ.1)
  refine ⟨144*C,mul_pos (by norm_num) hC,?_⟩
  intro n a b w K M r hz hmax T hT
  let μ := Measure.pi (fun _ : PathLabel n => gaussianReal 0 1)
  have hcounts : M=(n+2)*3+(n+1)*(3*3) := by
    simp only [M,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
  have hK : K ≤ M := by dsimp only [K]; omega
  have hM : 1 ≤ M := by omega
  have hMhi : (M:ℝ) ≤ 12*(K:ℝ) := by exact_mod_cast (show M ≤ 12*K by dsimp only [K]; omega)
  have hM₁ : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hr : 0 < r := half_pos (div_pos hβ.1 (by positivity))
  have hr₁ : r ≤ 1/4 := by
    have hden := one_le_mul_of_one_le_of_one_le hM₁ (one_le_pow₀ (by norm_num : (1:ℝ)≤3) (n:=K))
    have h := (div_le_self hβ.1.le hden).trans hβ.2
    dsimp only [r]; linarith only [h]

  let S := transverseLabels a b
  let i₀ : PathLabel n := .inl (a.succ,2)
  have hz₀ (l) (hl : l∈S) : w l=0 := by
    apply hz
    rcases Finset.mem_union.mp hl with hl|hl
    · rcases Finset.mem_union.mp hl with hl|hl
      · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hl; exact (Finset.mem_erase.mp hp).1
      · obtain ⟨⟨p,j⟩,hp,rfl⟩ := Finset.mem_image.mp hl
        exact fun h => (Finset.mem_erase.mp (Finset.mem_product.mp hp).2).1 (congrArg Prod.snd h)
    · obtain ⟨⟨p,j⟩,hp,rfl⟩ := Finset.mem_image.mp hl
      exact fun h => (Finset.mem_erase.mp (Finset.mem_product.mp hp).1).1 (congrArg Prod.fst h)

  obtain ⟨E,hE,hfloor,hwidth⟩ := gapped_box_relative_widths i₀ S (transverseLabels_card a b) w.ofLp hz₀
    (by positivity : 0 ≤ 2*(M:ℝ)+3) hmax hr (hr₁.trans (by norm_num)) T hT
  refine ⟨E,hE,?_,hwidth⟩
  have hbase : 2*f*r=f*β/((M:ℝ)*3^K) := by dsimp only [r]; ring
  change (2*f*r)^M*exp (-(9*(M:ℝ)+(2*(M:ℝ)+3+3)^2)/2) ≤ ((1800:ℝ)^14*T^7)*μ.real E at hfloor
  rw [hbase,show 2*(M:ℝ)+3+3=2*(M:ℝ)+6 by ring] at hfloor
  have hlow := (hprice M K hM hK).trans ((div_le_iff₀ (by positivity)).mpr
      (hfloor.trans_eq (by ring : ((1800:ℝ)^14*T^7)*μ.real E=(T^7*μ.real E)*1800^14)))
  have hsq := pow_le_pow_left₀ (Nat.cast_nonneg M) hMhi 2
  exact (exp_le_exp.mpr (by nlinarith only [mul_le_mul_of_nonneg_left hsq hC.le])).trans hlow

#print axioms priced_transverse_widths
end
end GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
