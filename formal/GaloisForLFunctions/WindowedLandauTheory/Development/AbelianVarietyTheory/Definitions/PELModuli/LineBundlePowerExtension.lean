import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.StalkAffineGluing

/-! A section of a bundle power on a principal open extends after clearing a power of the denominator. -/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace GlobalTheory.AmpleLocal

variable {Z : Scheme.{0}}

def Sc {ι : Type} (U : ι → Z.Opens) (G : ι → Fn Z) (W : Z.Opens) (n : ℕ) (F : Fn Z) : Prop :=
  ∀ i, G i ^ n * F ∈ Reg (W ⊓ U i)

section Bundle

variable {ι : Type} {U : ι → Z.Opens} {G : ι → Fn Z}

theorem Sc.mono {V W : Z.Opens} {n : ℕ} {F : Fn Z} (h : Sc U G W n F) (hle : V ≤ W) : Sc U G V n F :=
  fun i => reg_mono (inf_le_inf_right _ hle) (h i)

theorem Sc.mul {W : Z.Opens} {n m : ℕ} {F F' : Fn Z} (h : Sc U G W n F) (h' : Sc U G W m F') :
    Sc U G W (n + m) (F * F') := fun i => by
  rw [pow_add, mul_mul_mul_comm]; exact mul_mem (h i) (h' i)

theorem Sc.pow {W : Z.Opens} {n : ℕ} {F : Fn Z} (h : Sc U G W n F) (d : ℕ) : Sc U G W (n * d) (F ^ d) := fun i => by
  rw [pow_mul, ← mul_pow]; exact pow_mem (h i) d

theorem Sc.zero (W : Z.Opens) (n : ℕ) : Sc U G W n 0 := fun i => by rw [mul_zero]; exact zero_mem _

variable (hU : ∀ z, ∃ i, z ∈ U i) (hG : ∀ i z, IsUnit (G i z))
include hU hG

theorem Sc.exists_loc {W : Z.Opens} {n : ℕ} {F : Fn Z} (h : Sc U G W n F) : ∃ D, IsLoc D W F := by
  choose D hD using fun i => AmpleLocal.exists_loc (h i)
  refine ⟨⨆ i, D i, fun z => Opens.mem_iSup.trans ⟨fun ⟨i, hi⟩ => ?_, fun ⟨hz, hu⟩ => ?_⟩⟩
  · exact ⟨((hD i).le hi).1, isUnit_of_mul_isUnit_right ((hD i).unit hi)⟩
  · obtain ⟨i, hi⟩ := hU z
    exact ⟨i, (hD i z).2 ⟨⟨hz, hi⟩, ((hG i z).pow n).mul hu⟩⟩

theorem Sc.ratio {D W : Z.Opens} {n : ℕ} {F σ : Fn Z} (h : Sc U G W n F) (hσ : Sc U G W n σ) (hD : IsLoc D W σ) :
    F * inv σ ∈ Reg D := by
  refine reg_glue fun z hz => ?_
  obtain ⟨i, hi⟩ := hU z
  have le : D ⊓ U i ≤ W ⊓ U i := inf_le_inf_right _ hD.le
  refine ⟨D ⊓ U i, ⟨hz, hi⟩, reg_congr (mul_mem (reg_mono le (h i)) (reg_inv (reg_mono le (hσ i))
    fun y hy => ((hG i y).pow n).mul (hD.unit hy.1))) fun y _ => ?_⟩
  show G i y ^ n * F y * Ring.inverse (G i y ^ n * σ y) = F y * Ring.inverse (σ y)
  have := Ring.mul_inverse_cancel _ ((hG i y).pow n)
  rw [Ring.mul_inverse_rev]
  linear_combination (F y * Ring.inverse (σ y)) * this

/-- Clear denominators on a finite trivializing cover and glue the resulting sections. -/
theorem Sc.extend [CompactSpace Z] [QuasiSeparatedSpace Z] (hT : ∀ i j, G i * inv (G j) ∈ Reg (U i ⊓ U j))
    {W : Z.Opens} {f : Fn Z} (hf : f ∈ Reg ⊤) (hW : IsLoc W ⊤ f) {n : ℕ} {F : Fn Z} (h : Sc U G W n F) :
    ∃ k : ℕ, ∃ σ, Sc U G ⊤ n σ ∧ ∀ z ∈ W, σ z = f z ^ k * F z := by
  classical
  choose c hc using hU
  choose V₀ hV₀ hm hle using fun z => exists_isAffineOpen_mem_and_subset (X := Z) (U := U (c z)) (x := z) (hc z)
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun z => (V₀ z : Set Z)) (fun z => (V₀ z).isOpen)
    (fun z _ => Set.mem_iUnion.2 ⟨z, hm z⟩)
  let V : s → Z.Opens := fun α => V₀ α.1
  have hV : ∀ α, IsAffineOpen (V α) := fun α => hV₀ α.1
  let e : s → ι := fun α => c α.1
  have he : ∀ α, V α ≤ U (e α) := fun α => hle α.1
  have cov : ∀ z, ∃ α, z ∈ V α := fun z => by
    obtain ⟨α, hα, h⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ z))
    exact ⟨⟨α, hα⟩, h⟩
  have loc : ∀ O : Z.Opens, IsLoc (W ⊓ O) O f := fun O z =>
    ⟨fun hz => ⟨hz.2, hW.unit hz.1⟩, fun hz => ⟨(hW z).2 ⟨trivial, hz.2⟩, hz.1⟩⟩
  have cancel : ∀ i z, Ring.inverse (G i z) ^ n * G i z ^ n = 1 := fun i z => by
    rw [← mul_pow, Ring.inverse_mul_cancel _ (hG i z), one_pow]
  choose p H hH eH using fun α => frac (hV α) (loc (V α)) (reg_mono le_top hf)
    (reg_mono (inf_le_inf_left _ (he α)) (h (e α)))
  obtain ⟨k, hk⟩ := (Set.finite_range p).bddAbove
  let t : s → Fn Z := fun α => f ^ (k - p α) * H α * inv (G (e α)) ^ n
  have ht : ∀ α i, G i ^ n * t α ∈ Reg (U i ⊓ V α) := fun α i => by
    have : G i ^ n * t α = (G i * inv (G (e α))) ^ n * (f ^ (k - p α) * H α) := by simp only [t]; ring
    rw [this]
    exact mul_mem (pow_mem (reg_mono (inf_le_inf_left _ (he α)) (hT _ _)) _)
      (mul_mem (pow_mem (reg_mono le_top hf) _) (reg_mono inf_le_right (hH α)))
  have et : ∀ α, ∀ z ∈ W ⊓ V α, t α z = f z ^ k * F z := fun α z hz => by
    obtain ⟨q, hq⟩ := Nat.exists_eq_add_of_le (hk ⟨α, rfl⟩)
    show f z ^ (k - p α) * H α z * Ring.inverse (G (e α) z) ^ n = _
    rw [← eH α z hz, hq, Nat.add_sub_cancel_left]
    show f z ^ q * (f z ^ p α * (G (e α) z ^ n * F z)) * _ = _
    linear_combination (f z ^ (p α + q) * F z) * cancel (e α) z
  have hk2 : ∀ q : s × s, ∃ m : ℕ, ∀ z ∈ V q.1 ⊓ V q.2, f z ^ m * t q.1 z = f z ^ m * t q.2 z := fun ⟨α, β⟩ => by
    obtain ⟨m, hm⟩ := kill (W := V α ⊓ V β) (QuasiSeparatedSpace.inter_isCompact _ _ (V α).isOpen (hV α).isCompact
      (V β).isOpen (hV β).isCompact) (loc _) (reg_mono le_top hf)
      (sub_mem (reg_mono (le_inf (inf_le_left.trans (he α)) inf_le_left) (ht α (e α)))
        (reg_mono (le_inf (inf_le_left.trans (he α)) inf_le_right) (ht β (e α)))) (fun z hz => by
        show G (e α) z ^ n * t α z - G (e α) z ^ n * t β z = 0
        rw [et α z ⟨hz.1, hz.2.1⟩, et β z ⟨hz.1, hz.2.2⟩, sub_self])
    refine ⟨m, fun z hz => ?_⟩
    have h₁ := hm z hz
    change f z ^ m * (G (e α) z ^ n * t α z - G (e α) z ^ n * t β z) = 0 at h₁
    show f z ^ m * t α z = f z ^ m * t β z
    linear_combination Ring.inverse (G (e α) z) ^ n * h₁ - (f z ^ m * t α z - f z ^ m * t β z) * cancel (e α) z
  choose m hm using hk2
  obtain ⟨r, hr⟩ := (Set.finite_range m).bddAbove
  have agree : ∀ α β, ∀ z ∈ V α ⊓ V β, f z ^ r * t α z = f z ^ r * t β z := fun α β z hz => by
    obtain ⟨q, hq⟩ := Nat.exists_eq_add_of_le (hr ⟨(α, β), rfl⟩)
    rw [hq]
    linear_combination f z ^ q * hm (α, β) z hz
  choose a ha using cov
  refine ⟨r + k, fun z => f z ^ r * t (a z) z, fun i => reg_glue fun z hz => ⟨U i ⊓ V (a z), ⟨hz.2, ha z⟩, ?_⟩,
    fun z hz => ?_⟩
  · refine reg_congr (mul_mem (pow_mem (reg_mono le_top hf) r) (ht (a z) i)) fun y hy => ?_
    show f y ^ r * (G i y ^ n * t (a z) y) = G i y ^ n * (f y ^ r * t (a y) y)
    rw [← agree (a z) (a y) y ⟨hy.2, ha y⟩]; ring
  · show f z ^ r * t (a z) z = _
    rw [et _ z ⟨hz, ha z⟩]; ring

end Bundle

end GlobalTheory.AmpleLocal
