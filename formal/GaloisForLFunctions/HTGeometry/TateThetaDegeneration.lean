import GaloisForLFunctions.HTGeometry.QPochhammerZeroNome
import GaloisForLFunctions.HTGeometry.TateThetaGauge

/-!
# Tate-theta cusp degeneration and character limits
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Cancellation form of the Tate gauge: both surviving theta arguments approach zero. -/
theorem tateThetaGauge_eq_surviving_ratio (r : TateQuarterNome) (x : ℂ) (hx : x ≠ 0) :
    tateThetaGauge r x =
      x * multiplicativeTheta r.nome ((r.root : ℂ) ^ (3 : ℤ) * x) ^ 2 /
        multiplicativeTheta r.nome ((r.root : ℂ) ^ (1 : ℤ) * x) ^ 2 := by
  let u : ℂ := (r.root : ℂ) ^ (-1 : ℤ) * x
  let v : ℂ := (r.root : ℂ) ^ (3 : ℤ) * x
  let w : ℂ := (r.root : ℂ) ^ (1 : ℤ) * x
  have hu : u ≠ 0 := mul_ne_zero (zpow_ne_zero _ r.root_complex_ne_zero) hx
  have hqu : ((r.nome : EulerNome) : ℂ) * u = v := by
    simp only [u, v, TateQuarterNome.coe_nome]
    field_simp [r.root_complex_ne_zero]
  have hshift := multiplicativeTheta_mul_nome r.nome r.nome_ne_zero u hu
  rw [hqu] at hshift
  have hrel : multiplicativeTheta r.nome u =
      -u * multiplicativeTheta r.nome v := by
    rw [hshift]
    field_simp [hu]
  rw [tateThetaGauge]
  change -(r.root : ℂ) * multiplicativeTheta r.nome u *
      multiplicativeTheta r.nome v / multiplicativeTheta r.nome w ^ 2 =
    x * multiplicativeTheta r.nome v ^ 2 /
      multiplicativeTheta r.nome w ^ 2
  rw [hrel]
  congr 1
  simp only [u]
  field_simp [r.root_complex_ne_zero]

/-- The nome `r^4` tends to zero with its positive fourth root. -/
theorem tendsto_tateQuarterNome_nome_zero
    {ι : Type*} {l : Filter ι} (r : ι → TateQuarterNome)
    (hr : Tendsto (fun i => (r i).root) l (nhds 0)) :
    Tendsto (fun i => (((r i).nome : EulerNome) : ℂ)) l (nhds 0) := by
  convert hr.ofReal.pow 4 using 1 <;> norm_num

/-- First surviving theta factor tends to one along every moving point converging inside `ℂˣ`. -/
theorem tendsto_tateTheta_factor_one
    {ι : Type*} {l : Filter ι} (r : ι → TateQuarterNome) (x : ι → ℂ) (x₀ : ℂ)
    (hr : Tendsto (fun i => (r i).root) l (nhds 0))
    (hx : Tendsto x l (nhds x₀)) (hx₀ : x₀ ≠ 0) :
    Tendsto
      (fun i => multiplicativeTheta (r i).nome ((r i).root * x i))
      l (nhds 1) := by
  have hrC := hr.ofReal
  have ha : Tendsto (fun i => ((r i).root : ℂ) * x i) l (nhds 0) := by
    convert hrC.mul hx using 1 <;> norm_num
  have hb : Tendsto (fun i => ((r i).root : ℂ) ^ 3 / x i) l (nhds 0) := by
    convert (hrC.pow 3).div hx hx₀ using 1
    · rfl
    · norm_num
  apply tendsto_multiplicativeTheta_one_of_tendsto_zero
    (fun i => ((r i).root : ℂ) * x i)
    (fun i => ((r i).root : ℂ) ^ 3 / x i) (fun i => (r i).nome)
    ha hb (tendsto_tateQuarterNome_nome_zero r hr)
  intro i
  rw [TateQuarterNome.coe_nome]
  field_simp [(r i).root_complex_ne_zero]

/-- Third surviving theta factor tends to one along every moving point converging inside `ℂˣ`. -/
theorem tendsto_tateTheta_factor_three
    {ι : Type*} {l : Filter ι} (r : ι → TateQuarterNome) (x : ι → ℂ) (x₀ : ℂ)
    (hr : Tendsto (fun i => (r i).root) l (nhds 0))
    (hx : Tendsto x l (nhds x₀)) (hx₀ : x₀ ≠ 0) :
    Tendsto
      (fun i => multiplicativeTheta (r i).nome ((r i).root ^ 3 * x i))
      l (nhds 1) := by
  have hrC := hr.ofReal
  have ha : Tendsto (fun i => ((r i).root : ℂ) ^ 3 * x i) l (nhds 0) := by
    convert (hrC.pow 3).mul hx using 1 <;> norm_num
  have hb : Tendsto (fun i => ((r i).root : ℂ) / x i) l (nhds 0) := by
    convert hrC.div hx hx₀ using 1
    · rfl
    · norm_num
  apply tendsto_multiplicativeTheta_one_of_tendsto_zero
    (fun i => ((r i).root : ℂ) ^ 3 * x i)
    (fun i => ((r i).root : ℂ) / x i) (fun i => (r i).nome)
    ha hb (tendsto_tateQuarterNome_nome_zero r hr)
  intro i
  rw [TateQuarterNome.coe_nome]
  field_simp [(r i).root_complex_ne_zero]

/-- **Cusp degeneration.** The Tate-theta gauge converges to the boundary character `x`, even
along arbitrary moving points converging to a nonzero limit. -/
theorem tendsto_tateThetaGauge_of_root_zero
    {ι : Type*} {l : Filter ι} (r : ι → TateQuarterNome) (x : ι → ℂ) (x₀ : ℂ)
    (hr : Tendsto (fun i => (r i).root) l (nhds 0))
    (hx : Tendsto x l (nhds x₀)) (hx₀ : x₀ ≠ 0) :
    Tendsto (fun i => tateThetaGauge (r i) (x i)) l (nhds x₀) := by
  have h1 := tendsto_tateTheta_factor_one r x x₀ hr hx hx₀
  have h3 := tendsto_tateTheta_factor_three r x x₀ hr hx hx₀
  have hratio : Tendsto
      (fun i => x i *
        multiplicativeTheta (r i).nome ((r i).root ^ 3 * x i) ^ 2 /
          multiplicativeTheta (r i).nome ((r i).root * x i) ^ 2)
      l (nhds x₀) := by
    have h := hx.mul (h3.pow 2) |>.div (h1.pow 2) (pow_ne_zero 2 one_ne_zero)
    convert h using 1
    · rfl
    · norm_num
  refine hratio.congr' ?_
  filter_upwards [hx.eventually_ne hx₀] with i hxi
  rw [tateThetaGauge_eq_surviving_ratio (r i) (x i) hxi]
  simp
  rfl

/-- Pointwise form of the cusp limit. -/
theorem tendsto_tateThetaGauge_pointwise_of_root_zero
    {ι : Type*} {l : Filter ι} (r : ι → TateQuarterNome)
    (hr : Tendsto (fun i => (r i).root) l (nhds 0)) (x : ℂ) (hx : x ≠ 0) :
    Tendsto (fun i => tateThetaGauge (r i) x) l (nhds x) :=
  tendsto_tateThetaGauge_of_root_zero r (fun _ => x) x hr tendsto_const_nhds hx

/-- The pointing value is eventually nonzero at the Tate cusp. -/
theorem eventually_tateThetaGauge_one_ne_zero
    {ι : Type*} {l : Filter ι} (r : ι → TateQuarterNome)
    (hr : Tendsto (fun i => (r i).root) l (nhds 0)) :
    ∀ᶠ i in l, tateThetaGauge (r i) 1 ≠ 0 :=
  (tendsto_tateThetaGauge_pointwise_of_root_zero r hr 1 one_ne_zero).eventually_ne one_ne_zero

/-- Pointed integral-charge gauge. -/
def pointedTateThetaGauge (r : TateQuarterNome) (m : ℤ) (x : ℂ) : ℂ :=
  (tateThetaGauge r x / tateThetaGauge r 1) ^ m

/-- Every integral boundary character is attained in the cusp limit. -/
theorem tendsto_pointedTateThetaGauge_of_root_zero
    {ι : Type*} {l : Filter ι} (r : ι → TateQuarterNome)
    (hr : Tendsto (fun i => (r i).root) l (nhds 0)) (m : ℤ) (x : ℂ) (hx : x ≠ 0) :
    Tendsto (fun i => pointedTateThetaGauge (r i) m x) l (nhds (x ^ m)) := by
  have hxlim := tendsto_tateThetaGauge_pointwise_of_root_zero r hr x hx
  have h1lim := tendsto_tateThetaGauge_pointwise_of_root_zero r hr 1 one_ne_zero
  unfold pointedTateThetaGauge
  simpa using (hxlim.div h1lim one_ne_zero).zpow₀ m (Or.inl (by simpa using hx))

end

end GaloisForLFunctions.HTGeometry
