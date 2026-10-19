import GaloisForLFunctions.SquareRootThreshold.OffLineRunEdgeVisibilityLaw

/-!
# Periodic depth profiles: the Toeplitz visibility law

The ordinates are the lattice `2πk/L`. A **depth profile** of period `P` assigns to each residue
`r mod P` a depth `d_r ∈ [0, ½]`: the ordinate `2πk/L`, `k ≡ r`, carries the reflected pair
`½ ± d_r + 2πik/L`, a double on-line point when `d_r = 0`. The on-line lattice (`d = 0`) and the
off-line lattice (`P = 1`) are the two extreme profiles.

**Symbol formula** (`W_profileConfig`). Poisson summation on each residue class (a lattice of
spacing `2πP/L`, shifted by `2πr/L`) gives, for every compactly supported `C²` test, at every
aperture,

`W(f, f) = (L/P) Σ_m k(mL/P) D(m)`,  `D(m) = Σ_r 2 cosh(d_r mL/P) e^{2πirm/P}`,

with `k = f ⋆ f̃`. The configuration is seen only through the samples of `k` on the lag lattice
`(L/P)ℤ` and through the **depth symbol** `D`.

**Toeplitz law.** Writing `t = s + j L/P`, the lag sum becomes `∫₀^{L/P} Σ_{j,j'} f_j conj f_{j'}
D(j − j') ds` with `f_j = f(s + jL/P)`; a test of aperture `a` meets at most `n = ⌈2aP/L⌉`
consecutive lag points. Hence the profile is invisible at aperture `a` exactly when the `n × n`
Toeplitz matrix `[D(j − j')]` is positive semidefinite (`profileConfig_weil_nonneg_iff`): one
direction integrates the Toeplitz form over `s`, the other places narrow bumps at the lag points.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-! ### The profile configuration -/

/-- The lattice index `r + P j` of the residue `r` in period `j`. -/
def profileIndex (P : ℕ) (rj : Fin P × ℤ) : ℤ := (rj.1 : ℤ) + P * rj.2

theorem profileIndex_injective {P : ℕ} (hP : 0 < P) : Function.Injective (profileIndex P) := by
  rintro ⟨r, j⟩ ⟨r', j'⟩ h
  simp only [profileIndex] at h
  have hr : (r : ℤ) < P := by exact_mod_cast r.isLt
  have hr' : (r' : ℤ) < P := by exact_mod_cast r'.isLt
  have hP' : (0 : ℤ) < P := by exact_mod_cast hP
  have hjj : j = j' := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have : (P : ℤ) * j + P ≤ P * j' := by nlinarith
      omega
    · have : (P : ℤ) * j' + P ≤ P * j := by nlinarith
      omega
  subst hjj
  have : (r : ℤ) = r' := by linarith
  exact Prod.ext (Fin.ext (by exact_mod_cast this)) rfl

/-- The periodic depth-profile configuration: at the index `r + Pj` the points `½ ± d_r + i·ordinate`;
residues with `d_r = 0` carry one double on-line point. -/
def profileConfig {L : ℝ} (hL : 0 < L) {P : ℕ} (hP : 0 < P) (d : Fin P → ℝ)
    (hd0 : ∀ r, 0 ≤ d r) (hd1 : ∀ r, d r ≤ 1 / 2) : ZeroConfig where
  carrier := (Set.range fun rj : Fin P × ℤ => verticalLatticePoint L (d rj.1) (profileIndex P rj)) ∪
    Set.range fun rj : {rj : Fin P × ℤ // d rj.1 ≠ 0} =>
      verticalLatticePoint L (-d rj.1.1) (profileIndex P rj.1)
  mult := fun ρ => if ρ.re = 1 / 2 then 2 else 1
  one_le_mult := fun ρ _ => by split_ifs <;> norm_num
  strip := by
    rintro _ (⟨rj, rfl⟩ | ⟨rj, rfl⟩)
    · simp only [verticalLatticePoint]; constructor <;> linarith [hd0 rj.1, hd1 rj.1]
    · simp only [verticalLatticePoint]; constructor <;> linarith [hd0 rj.1.1, hd1 rj.1.1]
  reflect_mem := by
    rintro _ (⟨rj, rfl⟩ | ⟨rj, rfl⟩)
    · by_cases h : d rj.1 = 0
      · exact Or.inl ⟨rj, by simp only [reflect_verticalLatticePoint, h, neg_zero]⟩
      · exact Or.inr ⟨⟨rj, h⟩, (reflect_verticalLatticePoint _ _ _).symm⟩
    · exact Or.inl ⟨rj.1, by rw [reflect_verticalLatticePoint, neg_neg]⟩
  mult_reflect := by
    intro ρ _
    have hre : (reflect ρ).re = 1 - ρ.re := by simp [reflect]
    simp only [hre]
    by_cases h : ρ.re = 1 / 2
    · rw [if_pos h, if_pos (by linarith)]
    · rw [if_neg h, if_neg (fun h' => h (by linarith))]
  finite_window := by
    intro T₁ T₂
    have hF := finite_latticeWindow (h := 2 * π / L) (by positivity) T₁ T₂
    have hF' : {rj : Fin P × ℤ | T₁ < ((profileIndex P rj : ℤ) : ℝ) * (2 * π / L) ∧
        ((profileIndex P rj : ℤ) : ℝ) * (2 * π / L) ≤ T₂}.Finite :=
      hF.preimage (profileIndex_injective hP).injOn
    refine ((hF'.image fun rj => verticalLatticePoint L (d rj.1) (profileIndex P rj)).union
      (hF'.image fun rj => verticalLatticePoint L (-d rj.1) (profileIndex P rj))).subset ?_
    rintro _ ⟨(⟨rj, rfl⟩ | ⟨rj, rfl⟩), h1, h2⟩
    · exact Or.inl ⟨rj, ⟨h1, h2⟩, rfl⟩
    · exact Or.inr ⟨rj.1, ⟨h1, h2⟩, rfl⟩

/-! ### Poisson summation on a residue class -/

/-- A real shift of the Fourier variable is a modulation of the kernel. -/
theorem paperFT_add_ofReal (K : ℝ → ℂ) (c : ℝ) (z : ℂ) :
    paperFT K ((c : ℂ) + z) = paperFT (fun u => K u * cexp (I * c * u)) z := by
  rw [paperFT_def, paperFT_def]
  congr 1 with u
  rw [mul_assoc (K u) (cexp _) (cexp _), ← Complex.exp_add]
  congr 2
  ring

/-- The residue class `r mod P` is the lattice of spacing `2πP/L` shifted by `2πr/L`: its tilted
zero sum is `(L/P) Σ_m k(mL/P) e^{2πirm/P} e^{δ mL/P}`. -/
theorem hasSum_paperFT_residue {K : ℝ → ℂ} {A L : ℝ} (hL : 0 < L) {P : ℕ} (hP : 0 < P)
    (hK : ContDiff ℝ 2 K) (hsupp : ∀ u, K u ≠ 0 → |u| ≤ A) (r : Fin P) (δ : ℝ) :
    HasSum (fun j : ℤ => paperFT K ((((profileIndex P (r, j) : ℤ) : ℝ) * (2 * π / L) : ℝ) - I * δ))
      (((L / P : ℝ) : ℂ) * ∑' m : ℤ, K (m * (L / P)) * cexp (2 * π * I * r * m / P) *
        (Real.exp (δ * (m * (L / P))) : ℂ)) := by
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  have hℓ : 0 < L / P := div_pos hL hPr
  set c : ℝ := (r : ℝ) * (2 * π / L) with hc
  set Kr : ℝ → ℂ := fun u => K u * cexp (I * c * u) with hKr
  have hKrc : ContDiff ℝ 2 Kr :=
    hK.mul ((contDiff_const.mul Complex.ofRealCLM.contDiff).cexp)
  have hKrs : ∀ u, Kr u ≠ 0 → |u| ≤ A := fun u hu => hsupp u (left_ne_zero_of_mul hu)
  have h := hasSum_paperFT_lattice_sub_I_mul hℓ hKrc hKrs δ
  have hfun : (fun j : ℤ => paperFT Kr ((((j : ℝ) * (2 * π / (L / P)) : ℝ) : ℂ) - I * δ)) =
      fun j : ℤ => paperFT K ((((profileIndex P (r, j) : ℤ) : ℝ) * (2 * π / L) : ℝ) - I * δ) := by
    funext j
    rw [hKr, ← paperFT_add_ofReal]
    congr 1
    simp only [profileIndex, hc]
    push_cast
    field_simp
    ring
  have hval : ∀ m : ℤ, Kr (m * (L / P)) * (Real.exp (δ * (m * (L / P))) : ℂ) =
      K (m * (L / P)) * cexp (2 * π * I * r * m / P) * (Real.exp (δ * (m * (L / P))) : ℂ) := by
    intro m
    have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
    have hP0 : (P : ℂ) ≠ 0 := by exact_mod_cast hP.ne'
    rw [hKr]
    simp only
    congr 2
    rw [hc]
    push_cast
    congr 1
    field_simp
  rw [hfun] at h
  simp_rw [hval] at h
  exact h


/-! ### The symbol formula -/

/-- The depth symbol `D(m) = Σ_r 2 cosh(d_r mL/P) e^{2πirm/P}`. -/
def depthSymbol (L : ℝ) {P : ℕ} (d : Fin P → ℝ) (m : ℤ) : ℂ :=
  ∑ r : Fin P, ((2 * Real.cosh (d r * (m * (L / P))) : ℝ) : ℂ) * cexp (2 * π * I * r * m / P)

/-- Fibre sums over `Fin P × ℤ` add up. -/
theorem hasSum_fin_prod {P : ℕ} {F : Fin P × ℤ → ℂ} {S : Fin P → ℂ}
    (h : ∀ r, HasSum (fun j => F (r, j)) (S r)) : HasSum F (∑ r, S r) := by
  classical
  have hG : ∀ r ∈ (Finset.univ : Finset (Fin P)),
      HasSum (fun rj : Fin P × ℤ => if rj.1 = r then F rj else 0) (S r) := by
    intro r _
    have hinj : Function.Injective (fun j : ℤ => (r, j)) := fun j j' h => (Prod.ext_iff.mp h).2
    rw [← hinj.hasSum_iff]
    · have hc : ((fun rj : Fin P × ℤ => if rj.1 = r then F rj else 0) ∘ fun j => (r, j)) =
          fun j => F (r, j) := by funext j; simp
      rw [hc]; exact h r
    · rintro ⟨r', j⟩ hx
      have : r' ≠ r := fun hr => hx ⟨j, by rw [hr]⟩
      simp [this]
  have hsum := hasSum_sum hG
  have hfun : (fun rj : Fin P × ℤ => ∑ r ∈ Finset.univ, if rj.1 = r then F rj else 0) = F := by
    funext rj
    rw [Finset.sum_ite_eq]
    simp
  rw [hfun] at hsum
  exact hsum

/-- Profile points with different indices are different, whatever their depths. -/
theorem profilePoint_eq_imp {L : ℝ} (hL : 0 < L) {P : ℕ} (hP : 0 < P) {δ₁ δ₂ : ℝ}
    {rj rj' : Fin P × ℤ}
    (h : verticalLatticePoint L δ₁ (profileIndex P rj) =
      verticalLatticePoint L δ₂ (profileIndex P rj')) : rj = rj' := by
  have him := congrArg Complex.im h
  simp only [verticalLatticePoint] at him
  have hh : (2 * π / L) ≠ 0 := by positivity
  have : ((profileIndex P rj : ℤ) : ℝ) = profileIndex P rj' := mul_right_cancel₀ hh him
  exact profileIndex_injective hP (by exact_mod_cast this)

/-- A lag sum of a function with finite support is the sum over a window `|m| ≤ M`. -/
theorem exists_lag_window {K : ℝ → ℂ} {A ℓ : ℝ} (hℓ : 0 < ℓ) (hsupp : ∀ u, K u ≠ 0 → |u| ≤ A) :
    ∃ S : Finset ℤ, ∀ m : ℤ, m ∉ S → K (m * ℓ) = 0 := by
  refine ⟨Finset.Icc (-⌈A / ℓ⌉) ⌈A / ℓ⌉, fun m hm => ?_⟩
  by_contra hne
  apply hm
  have h := hsupp _ hne
  rw [abs_mul, abs_of_pos hℓ, ← le_div_iff₀ hℓ] at h
  have h' : |m| ≤ ⌈A / ℓ⌉ := by
    have : (|m| : ℝ) ≤ ⌈A / ℓ⌉ := by
      calc (|m| : ℝ) = |(m : ℝ)| := rfl
        _ ≤ A / ℓ := h
        _ ≤ ⌈A / ℓ⌉ := Int.le_ceil _
    exact_mod_cast this
  rw [Finset.mem_Icc]
  exact ⟨by linarith [neg_abs_le m], by linarith [le_abs_self m]⟩

/-- **The symbol formula.** For every compactly supported `C²` test,
`W(f, f) = (L/P) Σ_m k(mL/P) D(m)`. -/
theorem W_profileConfig {L : ℝ} (hL : 0 < L) {P : ℕ} (hP : 0 < P) (d : Fin P → ℝ)
    (hd0 : ∀ r, 0 ≤ d r) (hd1 : ∀ r, d r ≤ 1 / 2) {f : ℝ → ℂ} {A : ℝ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-(A / 2)) (A / 2)) :
    (profileConfig hL hP d hd0 hd1).W f f =
      ((L / P : ℝ) : ℂ) * ∑' m : ℤ, EF.weilTest f f (m * (L / P)) * depthSymbol L d m := by
  set Z := profileConfig hL hP d hd0 hd1 with hZ
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  have hℓ : 0 < L / P := div_pos hL hPr
  have hfc := hasCompactSupport_of_tsupport_subset_Icc hfs
  have hK := EF.weilTest_contDiff hf hf.continuous hfc
  have hKs := weilTest_abs_le hfs hfs
  set K := EF.weilTest f f with hKdef
  -- the residue sums
  set E : Fin P → ℝ → ℂ := fun r δ => ∑' m : ℤ, K (m * (L / P)) * cexp (2 * π * I * r * m / P) *
    (Real.exp (δ * (m * (L / P))) : ℂ) with hE
  have hp : ∀ r : Fin P, HasSum (fun j : ℤ =>
      paperFT K ((((profileIndex P (r, j) : ℤ) : ℝ) * (2 * π / L) : ℝ) - I * d r))
      (((L / P : ℝ) : ℂ) * E r (d r)) := fun r => hasSum_paperFT_residue hL hP hK hKs r (d r)
  have hm : ∀ r : Fin P, HasSum (fun j : ℤ =>
      paperFT K ((((profileIndex P (r, j) : ℤ) : ℝ) * (2 * π / L) : ℝ) + I * d r))
      (((L / P : ℝ) : ℂ) * E r (-d r)) := by
    intro r
    have h := hasSum_paperFT_residue hL hP hK hKs r (-d r)
    have hfun : ∀ j : ℤ, paperFT K ((((profileIndex P (r, j) : ℤ) : ℝ) * (2 * π / L) : ℝ) -
        I * ((-d r : ℝ) : ℂ)) = paperFT K ((((profileIndex P (r, j) : ℤ) : ℝ) * (2 * π / L) : ℝ) +
        I * d r) := fun j => by rw [Complex.ofReal_neg]; ring_nf
    simp_rw [hfun] at h
    exact h
  -- the two pieces of the carrier
  have hmult : ∀ rj : Fin P × ℤ, Z.mult (verticalLatticePoint L (d rj.1) (profileIndex P rj)) =
      if d rj.1 = 0 then 2 else 1 := by
    intro rj
    show (if _ then 2 else 1) = _
    simp [verticalLatticePoint]
  have hA : HasSum (fun ρ : Set.range (fun rj : Fin P × ℤ =>
      verticalLatticePoint L (d rj.1) (profileIndex P rj)) => Z.Wsummand f f ρ)
      (∑ r, ((if d r = 0 then 2 else 1 : ℕ) : ℂ) * (((L / P : ℝ) : ℂ) * E r (d r))) := by
    have hinj : Function.Injective (fun rj : Fin P × ℤ =>
        verticalLatticePoint L (d rj.1) (profileIndex P rj)) :=
      fun rj rj' h => profilePoint_eq_imp hL hP h
    rw [hinj.hasSum_range_iff]
    refine hasSum_fin_prod fun r => ?_
    have := (hp r).mul_left ((if d r = 0 then 2 else 1 : ℕ) : ℂ)
    refine this.congr_fun ?_
    intro j
    simp only [Function.comp_apply]
    rw [Wsummand_verticalLatticePoint _ hf.continuous hf.continuous hfc hfc, hmult (r, j)]
  have hB : HasSum (fun ρ : Set.range (fun rj : {rj : Fin P × ℤ // d rj.1 ≠ 0} =>
      verticalLatticePoint L (-d rj.1.1) (profileIndex P rj.1)) => Z.Wsummand f f ρ)
      (∑ r, if d r = 0 then 0 else ((L / P : ℝ) : ℂ) * E r (-d r)) := by
    have hinj : Function.Injective (fun rj : {rj : Fin P × ℤ // d rj.1 ≠ 0} =>
        verticalLatticePoint L (-d rj.1.1) (profileIndex P rj.1)) :=
      fun rj rj' h => Subtype.ext (profilePoint_eq_imp hL hP h)
    rw [hinj.hasSum_range_iff]
    have hfull : HasSum (fun rj : Fin P × ℤ => if d rj.1 = 0 then 0 else
        paperFT K ((((profileIndex P rj : ℤ) : ℝ) * (2 * π / L) : ℝ) + I * d rj.1))
        (∑ r, if d r = 0 then 0 else ((L / P : ℝ) : ℂ) * E r (-d r)) := by
      refine hasSum_fin_prod fun r => ?_
      by_cases h0 : d r = 0
      · simp only [h0, if_true]; exact hasSum_zero
      · simp only [h0, if_false]; exact hm r
    have hsub := (hasSum_subtype_iff_indicator (s := {rj : Fin P × ℤ | d rj.1 ≠ 0})
      (f := fun rj : Fin P × ℤ => if d rj.1 = 0 then 0 else
        paperFT K ((((profileIndex P rj : ℤ) : ℝ) * (2 * π / L) : ℝ) + I * d rj.1))).mpr (by
      refine hfull.congr_fun fun rj => ?_
      by_cases h0 : d rj.1 = 0
      · simp [Set.indicator, h0]
      · simp [Set.indicator, h0])
    refine hsub.congr_fun fun rj => ?_
    simp only [Function.comp_apply]
    have hne := rj.2
    rw [Wsummand_verticalLatticePoint _ hf.continuous hf.continuous hfc hfc]
    have hm1 : Z.mult (verticalLatticePoint L (-d rj.1.1) (profileIndex P rj.1)) = 1 := by
      show (if _ then 2 else 1) = _
      rw [if_neg]
      simp only [verticalLatticePoint]
      intro h; apply hne; linarith
    rw [hm1, if_neg hne]
    push_cast
    ring_nf
    rfl
  have hd : Disjoint (Set.range fun rj : Fin P × ℤ =>
      verticalLatticePoint L (d rj.1) (profileIndex P rj))
      (Set.range fun rj : {rj : Fin P × ℤ // d rj.1 ≠ 0} =>
        verticalLatticePoint L (-d rj.1.1) (profileIndex P rj.1)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨rj, rfl⟩ ⟨rj', hrj'⟩
    have hre := congrArg Complex.re hrj'
    simp only [verticalLatticePoint] at hre
    have h0 := hd0 rj'.1.1
    have h1 := hd0 rj.1
    exact rj'.2 (by linarith)
  have hall := HasSum.add_disjoint (f := Z.Wsummand f f) hd hA hB
  have heq := hall.tsum_eq
  rw [ZeroConfig.W]
  refine heq.trans ?_
  -- combine the residues
  obtain ⟨S, hS⟩ := exists_lag_window (K := K) hℓ hKs
  have hEsum : ∀ r δ, E r δ = ∑ m ∈ S, K (m * (L / P)) * cexp (2 * π * I * r * m / P) *
      (Real.exp (δ * (m * (L / P))) : ℂ) := fun r δ =>
    tsum_eq_sum fun m hm => by rw [hS m hm, zero_mul, zero_mul]
  rw [tsum_eq_sum (s := S) fun m hm => by rw [hS m hm, zero_mul], ← Finset.sum_add_distrib]
  have hres : ∀ r : Fin P, ((if d r = 0 then 2 else 1 : ℕ) : ℂ) * (((L / P : ℝ) : ℂ) * E r (d r)) +
      (if d r = 0 then 0 else ((L / P : ℝ) : ℂ) * E r (-d r)) =
      ((L / P : ℝ) : ℂ) * (E r (d r) + E r (-d r)) := by
    intro r
    by_cases h0 : d r = 0
    · simp only [h0, if_true, neg_zero]; push_cast; ring
    · simp only [h0, if_false]; push_cast; ring
  simp_rw [hres, hEsum, ← Finset.mul_sum, ← Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [depthSymbol, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Real.cosh_eq]
  push_cast
  ring_nf


/-! ### The Toeplitz form and the bump test -/

/-- The Toeplitz form `Σ_{j,j'} c_j conj(c_{j'}) D(j − j')` on `ℂⁿ`. -/
def toeplitzForm (D : ℤ → ℂ) (n : ℕ) (c : Fin n → ℂ) : ℂ :=
  ∑ j : Fin n, ∑ j' : Fin n, c j * conj (c j') * D ((j : ℤ) - j')

/-- The lag points `(i − (n−1)/2) ℓ` of the bump test. -/
def lagPoint (n : ℕ) (ℓ : ℝ) (i : Fin n) : ℝ := ((i : ℝ) - ((n : ℝ) - 1) / 2) * ℓ

theorem abs_lagPoint_le {n : ℕ} {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (i : Fin n) :
    |lagPoint n ℓ i| ≤ ((n : ℝ) - 1) / 2 * ℓ := by
  have hi : (i : ℝ) ≤ (n : ℝ) - 1 := by
    have : (i : ℕ) + 1 ≤ n := i.isLt
    have : ((i : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast this
    linarith
  have hi0 : (0 : ℝ) ≤ i := by positivity
  rw [lagPoint, abs_mul, abs_of_nonneg hℓ]
  gcongr
  rw [abs_le]
  constructor <;> linarith

theorem lagPoint_sub (n : ℕ) (ℓ : ℝ) (i i' : Fin n) :
    lagPoint n ℓ i - lagPoint n ℓ i' = (((i : ℤ) - i' : ℤ) : ℝ) * ℓ := by
  simp only [lagPoint]
  push_cast
  ring

/-- **Bump test.** Narrow bumps at the lag points with weights `c_i` turn the symbol formula into
the Toeplitz form: `W(f, f) = (L/P) B Σ_{i,i'} c_i conj(c_{i'}) D(i − i')` with `B > 0`. -/
theorem exists_W_profileConfig_eq_toeplitz {L : ℝ} (hL : 0 < L) {P : ℕ} (hP : 0 < P)
    (d : Fin P → ℝ) (hd0 : ∀ r, 0 ≤ d r) (hd1 : ∀ r, d r ≤ 1 / 2) {a : ℝ} {n : ℕ}
    (hna : ((n : ℝ) - 1) * (L / P) < 2 * a) (c : Fin n → ℂ) :
    ∃ f : ℝ → ℂ, ∃ B : ℝ, 0 < B ∧ ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧
      (profileConfig hL hP d hd0 hd1).W f f =
        ((L / P : ℝ) : ℂ) * (B : ℂ) * toeplitzForm (depthSymbol L d) n c := by
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  set ℓ : ℝ := L / P with hℓdef
  have hℓ : 0 < ℓ := div_pos hL hPr
  have hgap : 0 < a - ((n : ℝ) - 1) / 2 * ℓ := by linarith
  set w : ℝ := min (ℓ / 2) (a - ((n : ℝ) - 1) / 2 * ℓ) / 2 with hw
  have hw0 : 0 < w := by rw [hw]; exact half_pos (lt_min (by linarith) hgap)
  have hwℓ : 2 * w < ℓ := by
    have := min_le_left (ℓ / 2) (a - ((n : ℝ) - 1) / 2 * ℓ); rw [hw]; linarith
  have hwa : ((n : ℝ) - 1) / 2 * ℓ + w ≤ a := by
    have := min_le_right (ℓ / 2) (a - ((n : ℝ) - 1) / 2 * ℓ); rw [hw]; linarith
  obtain ⟨b, hbr⟩ : ∃ b : ContDiffBump (0 : ℝ), b.rOut = w :=
    ⟨⟨w / 2, w, half_pos hw0, half_lt_self hw0⟩, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℝ → ℝ, β = ⇑b := ⟨_, rfl⟩
  have hβc : ContDiff ℝ 2 β := hβ ▸ b.contDiff
  have hβs : ∀ x, β x ≠ 0 → |x| < w := by
    intro x hx
    have : x ∈ Function.support b := by rw [← hβ]; exact hx
    rw [b.support_eq, hbr, Metric.mem_ball, Real.dist_eq, sub_zero] at this
    exact this
  have hβcs : HasCompactSupport β := hβ ▸ b.hasCompactSupport
  set B : ℝ := ∫ x, β x * β x with hB
  have hβi : Integrable fun x => β x * β x :=
    (hβc.continuous.mul hβc.continuous).integrable_of_hasCompactSupport hβcs.mul_right
  have hBpos : 0 < B := by
    rw [hB, integral_pos_iff_support_of_nonneg (fun x => mul_self_nonneg (β x)) hβi,
      Function.support_mul, Set.inter_self, hβ, b.support_eq, hbr]
    exact Metric.measure_ball_pos volume 0 hw0
  set f : ℝ → ℂ := fun t => ∑ i : Fin n, c i * (β (t - lagPoint n ℓ i) : ℂ) with hf
  have hfc : ContDiff ℝ 2 f := by
    rw [hf]
    refine ContDiff.sum fun i _ => contDiff_const.mul ?_
    exact Complex.ofRealCLM.contDiff.comp (hβc.comp (contDiff_id.sub contDiff_const))
  have hfsupp : ∀ t, f t ≠ 0 → |t| < a := by
    intro t ht
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero ht
    have hb : β (t - lagPoint n ℓ i) ≠ 0 := fun h0 => hi (by rw [h0]; simp)
    have h1 := hβs _ hb
    have h2 := abs_lagPoint_le hℓ.le i
    calc |t| = |(t - lagPoint n ℓ i) + lagPoint n ℓ i| := by ring_nf
      _ ≤ |t - lagPoint n ℓ i| + |lagPoint n ℓ i| := abs_add_le _ _
      _ < w + ((n : ℝ) - 1) / 2 * ℓ := by linarith
      _ ≤ a := by linarith
  have hfs : tsupport f ⊆ Icc (-a) a := by
    refine closure_minimal ?_ isClosed_Icc
    intro t ht
    have := hfsupp t ht
    exact ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
  refine ⟨f, B, hBpos, hfc, hfs, ?_⟩
  -- the Weil kernel at the lag lattice
  have hcross : ∀ (m : ℤ) (i i' : Fin n), (∫ t, (β (t - lagPoint n ℓ i) : ℂ) *
      (β (t - m * ℓ - lagPoint n ℓ i') : ℂ)) = if (i : ℤ) - i' = m then (B : ℂ) else 0 := by
    intro m i i'
    split_ifs with hm
    · have hsh : ∀ t, t - m * ℓ - lagPoint n ℓ i' = t - lagPoint n ℓ i := by
        intro t
        have := lagPoint_sub n ℓ i i'
        rw [hm] at this
        linarith
      simp_rw [hsh]
      rw [hB, ← integral_complex_ofReal]
      push_cast
      exact integral_sub_right_eq_self (fun t => ((β t : ℝ) : ℂ) * (β t : ℂ)) _
    · have hz : ∀ t, (β (t - lagPoint n ℓ i) : ℂ) * (β (t - m * ℓ - lagPoint n ℓ i') : ℂ) = 0 := by
        intro t
        by_contra hne
        have h1 := hβs (t - lagPoint n ℓ i) (fun h0 => hne (by rw [h0]; simp))
        have h2 := hβs (t - m * ℓ - lagPoint n ℓ i') (fun h0 => hne (by rw [h0]; simp))
        have hk : ((i : ℤ) - i' - m : ℤ) ≠ 0 := sub_ne_zero.mpr hm
        have hk1 : (1 : ℝ) ≤ |(((i : ℤ) - i' - m : ℤ) : ℝ)| := by
          rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hk
        have hdiff : (((i : ℤ) - i' - m : ℤ) : ℝ) * ℓ =
            (t - m * ℓ - lagPoint n ℓ i') - (t - lagPoint n ℓ i) := by
          have := lagPoint_sub n ℓ i i'
          push_cast at this ⊢
          linarith
        have : |(((i : ℤ) - i' - m : ℤ) : ℝ) * ℓ| < 2 * w := by
          rw [hdiff]
          calc |(t - m * ℓ - lagPoint n ℓ i') - (t - lagPoint n ℓ i)|
              ≤ |t - m * ℓ - lagPoint n ℓ i'| + |t - lagPoint n ℓ i| := abs_sub _ _
            _ < w + w := add_lt_add h2 h1
            _ = 2 * w := by ring
        rw [abs_mul, abs_of_pos hℓ] at this
        nlinarith
      simp_rw [hz, integral_zero]
  have hK : ∀ m : ℤ, EF.weilTest f f (m * ℓ) =
      ∑ i : Fin n, ∑ i' : Fin n, if (i : ℤ) - i' = m then c i * conj (c i') * (B : ℂ) else 0 := by
    intro m
    rw [weilTest_apply]
    have hpt : ∀ t, f t * conj (f (t - m * ℓ)) = ∑ i : Fin n, ∑ i' : Fin n,
        c i * conj (c i') * ((β (t - lagPoint n ℓ i) : ℂ) *
          (β (t - m * ℓ - lagPoint n ℓ i') : ℂ)) := by
      intro t
      rw [hf]
      simp only
      rw [map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
      rw [map_mul, Complex.conj_ofReal]
      ring
    simp_rw [hpt]
    have hint : ∀ i i' : Fin n, Integrable fun t => c i * conj (c i') *
        ((β (t - lagPoint n ℓ i) : ℂ) * (β (t - m * ℓ - lagPoint n ℓ i') : ℂ)) := by
      intro i i'
      refine Integrable.const_mul ?_ _
      refine ((Complex.continuous_ofReal.comp (hβc.continuous.comp (continuous_id.sub
        continuous_const))).mul (Complex.continuous_ofReal.comp (hβc.continuous.comp
        ((continuous_id.sub continuous_const).sub continuous_const)))).integrable_of_hasCompactSupport ?_
      refine HasCompactSupport.mul_right ?_
      exact (hβcs.comp_homeomorph (Homeomorph.subRight (lagPoint n ℓ i))).comp_left
        Complex.ofReal_zero
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun i' _ => hint i i']
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun i' _ => hint i i']
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [integral_const_mul, hcross m i i']
    split_ifs <;> ring
  -- the lag sum
  rw [W_profileConfig hL hP d hd0 hd1 (A := 2 * a) hfc (by rwa [show 2 * a / 2 = a by ring])]
  have hsum : HasSum (fun m : ℤ => EF.weilTest f f (m * ℓ) * depthSymbol L d m)
      (∑ i : Fin n, ∑ i' : Fin n, c i * conj (c i') * (B : ℂ) * depthSymbol L d ((i : ℤ) - i')) := by
    have hpt : ∀ m : ℤ, EF.weilTest f f (m * ℓ) * depthSymbol L d m = ∑ i : Fin n, ∑ i' : Fin n,
        if m = (i : ℤ) - i' then c i * conj (c i') * (B : ℂ) * depthSymbol L d ((i : ℤ) - i')
        else 0 := by
      intro m
      rw [hK m, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i' _ => ?_
      by_cases h : (i : ℤ) - i' = m
      · rw [if_pos h, if_pos h.symm, h]
      · rw [if_neg h, if_neg (fun h' => h h'.symm), zero_mul]
    simp_rw [hpt]
    exact hasSum_sum fun i _ => hasSum_sum fun i' _ => hasSum_ite_eq _ _
  rw [hsum.tsum_eq, toeplitzForm]
  simp only [hℓdef, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
  ring


/-! ### Toeplitz sums of finitely supported vectors -/

/-- The Toeplitz sum `Σ_{j,j' ∈ S} c_j conj(c_{j'}) D(j − j')`. -/
def toeplitzSum (D : ℤ → ℂ) (S : Finset ℤ) (c : ℤ → ℂ) : ℂ :=
  ∑ j ∈ S, ∑ j' ∈ S, c j * conj (c j') * D (j - j')

theorem toeplitzSum_subset {D : ℤ → ℂ} {S S' : Finset ℤ} (h : S ⊆ S') {c : ℤ → ℂ}
    (hc : ∀ j ∈ S', j ∉ S → c j = 0) : toeplitzSum D S c = toeplitzSum D S' c := by
  unfold toeplitzSum
  rw [Finset.sum_subset h fun j hj hjS => by
    rw [hc j hj hjS]; simp]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact Finset.sum_subset h fun j' hj' hj'S => by rw [hc j' hj' hj'S]; simp

/-- A sum over `n` consecutive integers starting at `k₀` is a sum over `Fin n`. -/
theorem sum_Ico_int_eq_sum_fin {M : Type*} [AddCommMonoid M] (k₀ : ℤ) (n : ℕ) (g : ℤ → M) :
    ∑ j ∈ Finset.Ico k₀ (k₀ + n), g j = ∑ i : Fin n, g (k₀ + i) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => g (k₀ + i)) n]
  refine Finset.sum_nbij' (fun j => (j - k₀).toNat) (fun i => k₀ + i) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_Ico, Finset.mem_range] at hj ⊢
    omega
  · intro i hi
    simp only [Finset.mem_Ico, Finset.mem_range] at hi ⊢
    omega
  · intro j hj
    simp only [Finset.mem_Ico] at hj
    omega
  · intro i _
    simp
  · intro j hj
    simp only [Finset.mem_Ico] at hj
    congr 1
    omega

/-- On a window of `n` consecutive indices the Toeplitz sum is the `n × n` Toeplitz form. -/
theorem toeplitzSum_Ico_eq (D : ℤ → ℂ) (k₀ : ℤ) (n : ℕ) (c : ℤ → ℂ) :
    toeplitzSum D (Finset.Ico k₀ (k₀ + n)) c = toeplitzForm D n fun i => c (k₀ + i) := by
  unfold toeplitzSum toeplitzForm
  rw [sum_Ico_int_eq_sum_fin]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sum_Ico_int_eq_sum_fin]
  refine Finset.sum_congr rfl fun j' _ => ?_
  congr 2
  ring

/-! ### The lag sum as an integral of Toeplitz sums -/

/-- Cutting `ℝ` into cells of length `ℓ`: `∫ f = Σ_n ∫₀^ℓ f(s + nℓ) ds`. -/
theorem hasSum_intervalIntegral_cells {f : ℝ → ℂ} (hf : Integrable f) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    HasSum (fun n : ℤ => ∫ s in (0 : ℝ)..ℓ, f (s + n * ℓ)) (∫ t, f t) := by
  have hg : Integrable fun x => f (ℓ * x) := hf.comp_mul_left' hℓ.ne'
  have h := hg.hasSum_intervalIntegral_comp_add_int
  have hint : ∫ x, f (ℓ * x) = ℓ⁻¹ * ∫ t, f t := by
    rw [Measure.integral_comp_mul_left, abs_of_pos (inv_pos.mpr hℓ), Complex.real_smul,
      Complex.ofReal_inv]
  have hcell : ∀ n : ℤ, ∫ x in (0 : ℝ)..1, f (ℓ * (x + n)) =
      ℓ⁻¹ * ∫ s in (0 : ℝ)..ℓ, f (s + n * ℓ) := by
    intro n
    have := intervalIntegral.integral_comp_mul_left (fun s => f (s + n * ℓ)) hℓ.ne'
      (a := 0) (b := 1)
    simp only [mul_zero, mul_one] at this
    rw [Complex.real_smul] at this
    rw [← this]
    congr 1 with x
    ring_nf
  simp_rw [hcell, hint] at h
  have := h.mul_left (ℓ : ℂ)
  have hℓ0 : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ.ne'
  simp only [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hℓ.ne',
    Complex.ofReal_one, one_mul] at this
  exact this

/-- **Periodization.** For a continuous test vanishing outside `(-a, a)`, with `Mℓ ≥ a + ℓ`, the lag
sum is an integral over one cell of Toeplitz sums of the samples `c_s(n) = f(s + nℓ)`:
`Σ_m k(mℓ) D(m) = ∫₀^ℓ Σ_{|n|,|n'| ≤ M} f(s + nℓ) conj f(s + n'ℓ) D(n − n') ds`. -/
theorem lagSum_eq_integral_toeplitzSum {f : ℝ → ℂ} (hf : Continuous f) {a ℓ : ℝ} (hℓ : 0 < ℓ)
    (hfz : ∀ t, a ≤ |t| → f t = 0) (D : ℤ → ℂ) {M : ℕ} (hM : a + ℓ ≤ M * ℓ) :
    ∑' m : ℤ, EF.weilTest f f (m * ℓ) * D m =
      ∫ s in (0 : ℝ)..ℓ, toeplitzSum D (Finset.Icc (-(M : ℤ)) M) (fun n => f (s + n * ℓ)) := by
  have hfz' : ∀ t, f t ≠ 0 → |t| < a := fun t ht => lt_of_not_ge fun h => ht (hfz t h)
  set W : Finset ℤ := Finset.Icc (-(M : ℤ)) M with hW
  set S : Finset ℤ := Finset.Icc (-(2 * (M : ℤ))) (2 * M) with hS
  -- samples vanish off the window `W` on the cell
  have hvan : ∀ s ∈ Icc (0 : ℝ) ℓ, ∀ n : ℤ, n ∉ W → f (s + n * ℓ) = 0 := by
    intro s hs n hn
    apply hfz
    rw [hW, Finset.mem_Icc, not_and_or, not_le, not_le] at hn
    rcases hn with h | h
    · have : (n : ℝ) ≤ -M - 1 := by exact_mod_cast (by omega : n ≤ -(M : ℤ) - 1)
      have h1 : (n : ℝ) * ℓ ≤ (-M - 1) * ℓ := mul_le_mul_of_nonneg_right this hℓ.le
      calc a ≤ -(s + n * ℓ) := by linarith [hs.2]
        _ ≤ |s + n * ℓ| := neg_le_abs _
    · have : (M : ℝ) + 1 ≤ n := by exact_mod_cast (by omega : (M : ℤ) + 1 ≤ n)
      have h1 : ((M : ℝ) + 1) * ℓ ≤ n * ℓ := mul_le_mul_of_nonneg_right this hℓ.le
      calc a ≤ s + n * ℓ := by linarith [hs.1]
        _ ≤ |s + n * ℓ| := le_abs_self _
  -- the kernel vanishes off the lag window `S`
  have hKz : ∀ m : ℤ, m ∉ S → EF.weilTest f f (m * ℓ) * D m = 0 := by
    intro m hm
    have hm' : 2 * (M : ℤ) + 1 ≤ |m| := by
      rw [hS, Finset.mem_Icc, not_and_or, not_le, not_le] at hm
      rcases hm with h | h
      · rw [abs_of_neg (by omega)]; omega
      · rw [abs_of_nonneg (by omega)]; omega
    have hm'' : (2 * M + 1 : ℝ) ≤ |(m : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast hm'
    rw [weilTest_apply]
    have : (fun t => f t * conj (f (t - m * ℓ))) = fun _ => 0 := by
      funext t
      by_contra hne
      have h1 := hfz' t (left_ne_zero_of_mul hne)
      have h2 := hfz' (t - m * ℓ) (fun h0 => hne (by rw [h0]; simp))
      have : |(m : ℝ) * ℓ| < 2 * a := by
        calc |(m : ℝ) * ℓ| = |t - (t - m * ℓ)| := by ring_nf
          _ ≤ |t| + |t - m * ℓ| := abs_sub _ _
          _ < a + a := add_lt_add h1 h2
          _ = 2 * a := by ring
      rw [abs_mul, abs_of_pos hℓ] at this
      nlinarith
    rw [this, integral_zero, zero_mul]
  rw [tsum_eq_sum hKz]
  -- each kernel sample as a finite sum over cells
  have hcell : ∀ m : ℤ, EF.weilTest f f (m * ℓ) = ∑ n ∈ W,
      ∫ s in (0 : ℝ)..ℓ, f (s + n * ℓ) * conj (f (s + (n - m : ℤ) * ℓ)) := by
    intro m
    have hg : Continuous fun t => f t * conj (f (t - m * ℓ)) :=
      hf.mul (continuous_conj.comp (hf.comp (continuous_id.sub continuous_const)))
    have hgs : HasCompactSupport fun t => f t * conj (f (t - m * ℓ)) := by
      refine HasCompactSupport.intro (isCompact_Icc (a := -a) (b := a)) fun t ht => ?_
      rw [hfz t (by
        by_contra hlt
        push Not at hlt
        exact ht ⟨by linarith [(abs_lt.mp hlt).1], by linarith [(abs_lt.mp hlt).2]⟩), zero_mul]
    have hsum := hasSum_intervalIntegral_cells (hg.integrable_of_hasCompactSupport hgs) hℓ
    rw [weilTest_apply, ← hsum.tsum_eq, tsum_eq_sum (s := W) fun n hn => ?_]
    · refine Finset.sum_congr rfl fun n _ => intervalIntegral.integral_congr fun s _ => ?_
      push_cast
      ring_nf
    · rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)) fun s hs => ?_,
        intervalIntegral.integral_zero]
      rw [Set.uIcc_of_le hℓ.le] at hs
      simp only
      rw [hvan s hs n hn, zero_mul]
  -- move the integral outside
  have hcont : ∀ n m : ℤ, Continuous fun s => f (s + n * ℓ) *
      conj (f (s + (n - m : ℤ) * ℓ)) * D m := fun n m =>
    ((hf.comp (continuous_id.add continuous_const)).mul
      (continuous_conj.comp (hf.comp (continuous_id.add continuous_const)))).mul continuous_const
  have hlhs : ∑ m ∈ S, EF.weilTest f f (m * ℓ) * D m = ∫ s in (0 : ℝ)..ℓ,
      ∑ m ∈ S, ∑ n ∈ W, f (s + n * ℓ) * conj (f (s + (n - m : ℤ) * ℓ)) * D m := by
    have h1 : ∀ m ∈ S, IntervalIntegrable (fun s => ∑ n ∈ W, f (s + n * ℓ) *
        conj (f (s + (n - m : ℤ) * ℓ)) * D m) volume 0 ℓ := fun m _ =>
      (continuous_finsetSum W fun n _ => hcont n m).intervalIntegrable _ _
    rw [intervalIntegral.integral_finsetSum h1]
    refine Finset.sum_congr rfl fun m _ => ?_
    have h2 : ∀ n ∈ W, IntervalIntegrable (fun s => f (s + n * ℓ) *
        conj (f (s + (n - m : ℤ) * ℓ)) * D m) volume 0 ℓ := fun n _ =>
      (hcont n m).intervalIntegrable _ _
    rw [intervalIntegral.integral_finsetSum h2, hcell m, Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [intervalIntegral.integral_mul_const]
  rw [hlhs]
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [Set.uIcc_of_le hℓ.le] at hs
  simp only [toeplitzSum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n hn => ?_
  -- reindex the lags `m` by the positions `n' = n − m`
  have hl : ∑ m ∈ S, f (s + n * ℓ) * conj (f (s + (n - m : ℤ) * ℓ)) * D m =
      ∑' m : ℤ, f (s + n * ℓ) * conj (f (s + (n - m : ℤ) * ℓ)) * D m := by
    symm
    refine tsum_eq_sum fun m hm => ?_
    rw [hvan s hs (n - m) fun hnm => hm ?_]
    · simp
    · rw [hW, Finset.mem_Icc] at hn hnm
      rw [hS, Finset.mem_Icc]
      constructor <;> omega
  have hr : ∑ n' ∈ W, f (s + n * ℓ) * conj (f (s + n' * ℓ)) * D (n - n') =
      ∑' n' : ℤ, f (s + n * ℓ) * conj (f (s + n' * ℓ)) * D (n - n') := by
    symm
    refine tsum_eq_sum fun n' hn' => ?_
    rw [hvan s hs n' hn']
    simp
  rw [hl, hr, ← (Equiv.subLeft n).tsum_eq]
  congr 1 with m
  simp only [Equiv.subLeft_apply, sub_sub_cancel]


/-! ### The Toeplitz visibility law -/

/-- A vector supported on a window of `n` consecutive indices has nonnegative Toeplitz sum when the
`n × n` Toeplitz form is positive semidefinite. -/
theorem re_toeplitzSum_nonneg_of_window {D : ℤ → ℂ} {n : ℕ}
    (hT : ∀ c : Fin n → ℂ, 0 ≤ (toeplitzForm D n c).re) {S : Finset ℤ} {c : ℤ → ℂ} (k₀ : ℤ)
    (hS : ∀ j, j ∉ S → c j = 0) (hV : ∀ j, (j < k₀ ∨ k₀ + n ≤ j) → c j = 0) :
    0 ≤ (toeplitzSum D S c).re := by
  have h1 : toeplitzSum D (S ∩ Finset.Ico k₀ (k₀ + n)) c = toeplitzSum D S c :=
    toeplitzSum_subset Finset.inter_subset_left fun j _ hj => hV j (by
      rw [Finset.mem_inter, Finset.mem_Ico, not_and_or, not_and_or, not_le, not_lt] at hj
      tauto)
  have h2 : toeplitzSum D (S ∩ Finset.Ico k₀ (k₀ + n)) c =
      toeplitzSum D (Finset.Ico k₀ (k₀ + n)) c :=
    toeplitzSum_subset Finset.inter_subset_right fun j hj hj' => hS j fun hjS =>
      hj' (Finset.mem_inter.mpr ⟨hjS, hj⟩)
  rw [← h1, h2, toeplitzSum_Ico_eq]
  exact hT _

/-- **Invisibility from Toeplitz positivity.** If the `n × n` Toeplitz form of the depth symbol is
positive semidefinite, `n = ⌈2a/(L/P)⌉`, the profile is Weil-nonnegative at aperture `a`. -/
theorem re_W_profileConfig_nonneg_of_toeplitz {L : ℝ} (hL : 0 < L) {P : ℕ} (hP : 0 < P)
    (d : Fin P → ℝ) (hd0 : ∀ r, 0 ≤ d r) (hd1 : ∀ r, d r ≤ 1 / 2) {a : ℝ}
    (hT : ∀ c : Fin ⌈2 * a / (L / P)⌉₊ → ℂ,
      0 ≤ (toeplitzForm (depthSymbol L d) ⌈2 * a / (L / P)⌉₊ c).re)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) :
    0 ≤ ((profileConfig hL hP d hd0 hd1).W f f).re := by
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  set ℓ : ℝ := L / P with hℓdef
  have hℓ : 0 < ℓ := div_pos hL hPr
  set n : ℕ := ⌈2 * a / ℓ⌉₊ with hn
  have hnℓ : 2 * a ≤ n * ℓ := by
    have := Nat.le_ceil (2 * a / ℓ)
    rwa [div_le_iff₀ hℓ] at this
  have hfz : ∀ t, a ≤ |t| → f t = 0 := fun t ht =>
    eq_zero_of_tsupport_subset_Icc hf.continuous hfs ht
  set M : ℕ := ⌈(a + ℓ) / ℓ⌉₊ with hM
  have hMℓ : a + ℓ ≤ M * ℓ := by
    have := Nat.le_ceil ((a + ℓ) / ℓ)
    rwa [div_le_iff₀ hℓ] at this
  rw [W_profileConfig hL hP d hd0 hd1 (A := 2 * a) hf (by rwa [show 2 * a / 2 = a by ring]),
    lagSum_eq_integral_toeplitzSum hf.continuous hℓ hfz _ hMℓ]
  have hcont : Continuous fun s => toeplitzSum (depthSymbol L d) (Finset.Icc (-(M : ℤ)) M)
      (fun k => f (s + k * ℓ)) := by
    unfold toeplitzSum
    refine continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun j' _ => ?_
    exact ((hf.continuous.comp (continuous_id.add continuous_const)).mul
      (continuous_conj.comp (hf.continuous.comp (continuous_id.add continuous_const)))).mul
        continuous_const
  rw [intervalIntegral.integral_of_le hℓ.le, Complex.re_ofReal_mul]
  refine mul_nonneg hℓ.le ?_
  rw [show (∫ s in Ioc (0 : ℝ) ℓ, toeplitzSum (depthSymbol L d) (Finset.Icc (-(M : ℤ)) M)
      (fun k => f (s + k * ℓ))).re = ∫ s in Ioc (0 : ℝ) ℓ, (toeplitzSum (depthSymbol L d)
      (Finset.Icc (-(M : ℤ)) M) (fun k => f (s + k * ℓ))).re from
    (integral_re (hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self)).symm]
  refine setIntegral_nonneg measurableSet_Ioc fun s hs => ?_
  -- the window of the samples at `s`
  set k₀ : ℤ := ⌊(-a - s) / ℓ⌋ + 1 with hk₀
  have hk₀lo : -a < s + k₀ * ℓ := by
    have h := Int.lt_floor_add_one ((-a - s) / ℓ)
    rw [div_lt_iff₀ hℓ] at h
    push_cast [hk₀]
    linarith
  refine re_toeplitzSum_nonneg_of_window hT k₀ (fun j hj => ?_) (fun j hj => ?_)
  · apply hfz
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hj
    rcases hj with h | h
    · have : (j : ℝ) ≤ -M - 1 := by exact_mod_cast (by omega : j ≤ -(M : ℤ) - 1)
      have h1 : (j : ℝ) * ℓ ≤ (-M - 1) * ℓ := mul_le_mul_of_nonneg_right this hℓ.le
      calc a ≤ -(s + j * ℓ) := by linarith [hs.2]
        _ ≤ |s + j * ℓ| := neg_le_abs _
    · have : (M : ℝ) + 1 ≤ j := by exact_mod_cast (by omega : (M : ℤ) + 1 ≤ j)
      have h1 : ((M : ℝ) + 1) * ℓ ≤ j * ℓ := mul_le_mul_of_nonneg_right this hℓ.le
      calc a ≤ s + j * ℓ := by linarith [hs.1]
        _ ≤ |s + j * ℓ| := le_abs_self _
  · apply hfz
    rcases hj with h | h
    · have hj : (j : ℝ) ≤ ⌊(-a - s) / ℓ⌋ := by exact_mod_cast (by omega : j ≤ ⌊(-a - s) / ℓ⌋)
      have h2 : (j : ℝ) ≤ (-a - s) / ℓ := hj.trans (Int.floor_le _)
      rw [le_div_iff₀ hℓ] at h2
      calc a ≤ -(s + j * ℓ) := by linarith
        _ ≤ |s + j * ℓ| := neg_le_abs _
    · have hj : (k₀ : ℝ) + n ≤ j := by exact_mod_cast h
      have h1 : ((k₀ : ℝ) + n) * ℓ ≤ j * ℓ := mul_le_mul_of_nonneg_right hj hℓ.le
      calc a ≤ s + j * ℓ := by nlinarith
        _ ≤ |s + j * ℓ| := le_abs_self _

/-- **Toeplitz visibility law.** A periodic depth profile is Weil-nonnegative at aperture `a`
if and only if the `n × n` Toeplitz matrix `[D(j − j')]` of its depth symbol is positive
semidefinite, where `n = ⌈2aP/L⌉` is the number of lag points of spacing `L/P` that a test of
aperture `a` can meet. -/
theorem profileConfig_weil_nonneg_iff {L : ℝ} (hL : 0 < L) {P : ℕ} (hP : 0 < P)
    (d : Fin P → ℝ) (hd0 : ∀ r, 0 ≤ d r) (hd1 : ∀ r, d r ≤ 1 / 2) {a : ℝ} (ha : 0 < a) :
    (∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
        0 ≤ ((profileConfig hL hP d hd0 hd1).W f f).re) ↔
      ∀ c : Fin ⌈2 * a * P / L⌉₊ → ℂ,
        0 ≤ (toeplitzForm (depthSymbol L d) ⌈2 * a * P / L⌉₊ c).re := by
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  have hconv : 2 * a * P / L = 2 * a / (L / P) := by field_simp
  rw [hconv]
  constructor
  · intro h c
    by_contra hneg
    push Not at hneg
    have hna : ((⌈2 * a / (L / P)⌉₊ : ℕ) - 1 : ℝ) * (L / P) < 2 * a := by
      have := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 2 * a / (L / P))
      have hℓ : 0 < L / P := div_pos hL hPr
      have : ((⌈2 * a / (L / P)⌉₊ : ℕ) - 1 : ℝ) < 2 * a / (L / P) := by linarith
      rwa [lt_div_iff₀ hℓ] at this
    obtain ⟨f, B, hB, hf, hfs, hW⟩ := exists_W_profileConfig_eq_toeplitz hL hP d hd0 hd1 hna c
    have := h f hf hfs
    rw [hW, show ((L / P : ℝ) : ℂ) * (B : ℂ) = ((L / P * B : ℝ) : ℂ) by push_cast; ring,
      Complex.re_ofReal_mul] at this
    have hpos : 0 < L / P * B := mul_pos (div_pos hL hPr) hB
    nlinarith
  · intro hT f hf hfs
    exact re_W_profileConfig_nonneg_of_toeplitz hL hP d hd0 hd1 hT hf hfs

end GaloisForLFunctions.SquareRootThreshold
