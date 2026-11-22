import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.ShortNorms.RayClass.IntegralRayClasses

/-! Generators congruent to one identify a ray class with a translated ideal lattice. -/

open NumberField GlobalTheory.Mem

noncomputable section

namespace GlobalTheory.Mem.PartialZeta

variable {K : Type} [Field K] [NumberField K]

theorem cls_iff {M : ℕ} (D : RayData K M) (c : D.G) (B I : Ideal (𝓞 K))
    (hB : IsCoprime B (Ideal.span {(M : 𝓞 K)})) (hB0 : B ≠ ⊥) (hc : D.cls B = c⁻¹)
    (hI : IsCoprime I (Ideal.span {(M : 𝓞 K)})) (hI0 : I ≠ ⊥) :
    D.cls I = c ↔ ∃ x : 𝓞 K, x - 1 ∈ Ideal.span {(M : 𝓞 K)} ∧ Ideal.span {x} = I * B := by
  constructor
  · intro h
    have hIB : D.cls (I * B) = 1 := by
      rw [D.cls_mul I B hI hB hI0 hB0, h, hc, mul_inv_cancel]
    obtain ⟨x, hx, hx1⟩ := (D.cls_eq_one_iff (hI.mul_left hB) (mul_ne_zero hI0 hB0)).mp hIB
    exact ⟨x, hx1, hx.symm⟩
  · rintro ⟨x, hx1, hx⟩
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [Ideal.span_singleton_eq_bot.2 rfl] at hx
      exact mul_ne_zero hI0 hB0 hx.symm
    have h1 : D.cls (I * B) = 1 := by rw [← hx]; exact D.cls_span hx0 hx1
    rw [D.cls_mul I B hI hB hI0 hB0, hc] at h1
    exact mul_inv_eq_one.1 h1

theorem lattice_bij {R : Type*} [CommRing R] (N B : Ideal R) (hB : IsCoprime B N)
    (e : Module.Basis (Fin 2) ℤ ↥(N * B)) (x₀ : R) (h0 : x₀ ∈ B) (h1 : x₀ - 1 ∈ N) :
    ∃ f : ℤ × ℤ ≃ {x : R // x ∈ B ∧ x - 1 ∈ N},
      ∀ p, (f p : R) = x₀ + p.1 * (e 0 : R) + p.2 * (e 1 : R) := by
  have hB' : N * B ≤ B := Ideal.mul_le_left
  have hN' : N * B ≤ N := Ideal.mul_le_right
  let g : ↥(N * B) ≃ {x : R // x ∈ B ∧ x - 1 ∈ N} :=
    { toFun := fun y => ⟨x₀ + y.1, B.add_mem h0 (hB' y.2), by
        rw [add_sub_right_comm]
        exact N.add_mem h1 (hN' y.2)⟩
      invFun := fun x => ⟨x.1 - x₀, by
        rw [← Ideal.inf_eq_mul_of_isCoprime hB.symm]
        refine ⟨?_, B.sub_mem x.2.1 h0⟩
        have e : x.1 - x₀ = (x.1 - 1) - (x₀ - 1) := by ring
        rw [e]
        exact N.sub_mem x.2.2 h1⟩
      left_inv := fun y => Subtype.ext (by change x₀ + y.1 - x₀ = y.1; simp)
      right_inv := fun x => Subtype.ext (by change x₀ + (x.1 - x₀) = x.1; simp) }
  refine ⟨(finTwoArrowEquiv ℤ).symm.trans (e.equivFun.symm.toEquiv.trans g), fun p => ?_⟩
  simp [g, Fin.sum_univ_two, zsmul_eq_mul, add_assoc]

omit [NumberField K] in
theorem ne_bot_of_coprime {M : ℕ} (hM : Ideal.span {(M : 𝓞 K)} ≠ ⊤) {I : Ideal (𝓞 K)}
    (hI : IsCoprime I (Ideal.span {(M : 𝓞 K)})) : I ≠ ⊥ := by
  rintro rfl
  rw [Ideal.isCoprime_iff_sup_eq, bot_sup_eq] at hI
  exact hM hI

private abbrev ClassIdeals {M : ℕ} (D : RayData K M) (c : D.G) :=
  {I : Ideal (𝓞 K) // IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧ D.cls I = c}

private abbrev CongruentUnits (K : Type) [Field K] (M : ℕ) :=
  {u : (𝓞 K)ˣ // (u : 𝓞 K) - 1 ∈ Ideal.span {(M : 𝓞 K)}}

private abbrev CongruenceCoset (B : Ideal (𝓞 K)) (M : ℕ) :=
  {x : 𝓞 K // x ∈ B ∧ x - 1 ∈ Ideal.span {(M : 𝓞 K)}}

private theorem exists_ideal_for_coset_point {M : ℕ} (hM : Ideal.span {(M : 𝓞 K)} ≠ ⊤)
    (D : RayData K M) (c : D.G) (B : Ideal (𝓞 K)) (hB : IsCoprime B (Ideal.span {(M : 𝓞 K)}))
    (hB0 : B ≠ ⊥) (hc : D.cls B = c⁻¹) (x : CongruenceCoset B M) :
    ∃ I : ClassIdeals D c, Ideal.span {(x : 𝓞 K)} = I.1 * B := by
  have hle : Ideal.span {(x : 𝓞 K)} ≤ B := (Ideal.span_singleton_le_iff_mem _).mpr x.2.1
  obtain ⟨I, hI⟩ := Ideal.dvd_iff_le.mpr hle
  have hxc : IsCoprime (Ideal.span {(x : 𝓞 K)}) (Ideal.span {(M : 𝓞 K)}) := by
    rw [Ideal.isCoprime_iff_sup_eq, Ideal.eq_top_iff_one]
    have h : x.1 - (x.1 - 1) = (1 : 𝓞 K) := by ring
    have hmem : x.1 - (x.1 - 1) ∈ Ideal.span {(x : 𝓞 K)} ⊔ Ideal.span {(M : 𝓞 K)} :=
      Ideal.sub_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self x.1))
        (Ideal.mem_sup_right x.2.2)
    rwa [h] at hmem
  have hIc : IsCoprime I (Ideal.span {(M : 𝓞 K)}) := by
    rw [hI] at hxc
    exact hxc.of_mul_left_right
  have hIB : Ideal.span {(x : 𝓞 K)} = I * B := hI.trans (mul_comm _ _)
  have hIcls : D.cls I = c :=
    (cls_iff D c B I hB hB0 hc hIc (ne_bot_of_coprime hM hIc)).mpr ⟨x.1, x.2.2, hIB⟩
  exact ⟨⟨I, hIc, hIcls⟩, hIB⟩

private theorem generatorMap_injective {M : ℕ} {D : RayData K M} {c : D.G}
    {B : Ideal (𝓞 K)} (hB0 : B ≠ ⊥) (g : ClassIdeals D c → 𝓞 K) (hg0 : ∀ I, g I ≠ 0)
    (F : ClassIdeals D c × CongruentUnits K M → CongruenceCoset B M)
    (hF : ∀ p, (F p : 𝓞 K) = (p.2.1 : 𝓞 K) * g p.1)
    (hspanF : ∀ p, Ideal.span {(F p : 𝓞 K)} = p.1.1 * B) :
    Function.Injective F := by
  rintro ⟨I, u⟩ ⟨I', u'⟩ h
  have h1 : I.1 * B = I'.1 * B := by
    rw [← hspanF (I, u), ← hspanF (I', u'), h]
  have hII : I = I' := Subtype.ext (mul_right_cancel₀ hB0 h1)
  subst I'
  have h2 : (u.1 : 𝓞 K) * g I = (u'.1 : 𝓞 K) * g I := by
    rw [← hF (I, u), ← hF (I, u'), h]
  exact Prod.ext rfl (Subtype.ext (Units.ext (mul_right_cancel₀ (hg0 I) h2)))

/-- Multiplying a generator of `IB` by a unit congruent to one parametrizes
the generators in the translated ideal lattice. -/
theorem gen_bij {M : ℕ} (hM : Ideal.span {(M : 𝓞 K)} ≠ ⊤) (D : RayData K M) (c : D.G)
    (B : Ideal (𝓞 K))
    (hB : IsCoprime B (Ideal.span {(M : 𝓞 K)})) (hB0 : B ≠ ⊥) (hc : D.cls B = c⁻¹) :
    ∃ f : ClassIdeals D c × CongruentUnits K M ≃ CongruenceCoset B M,
      ∀ p, Ideal.span {(f p : 𝓞 K)} = p.1.1 * B := by
  classical
  have hgen (I : ClassIdeals D c) :
      ∃ x : 𝓞 K, x - 1 ∈ Ideal.span {(M : 𝓞 K)} ∧ Ideal.span {x} = I.1 * B :=
    (cls_iff D c B I.1 hB hB0 hc I.2.1 (ne_bot_of_coprime hM I.2.1)).mp I.2.2
  choose g hg1 hg using hgen
  have hgB (I : ClassIdeals D c) : g I ∈ B := by
    have h : g I ∈ Ideal.span {g I} := Ideal.mem_span_singleton_self _
    rw [hg I] at h
    have hle : I.1 * B ≤ B := Ideal.mul_le_left
    exact hle h
  have hg0 (I : ClassIdeals D c) : g I ≠ 0 := by
    intro h
    have hprod := hg I
    rw [h, Ideal.span_singleton_eq_bot.mpr rfl] at hprod
    exact mul_ne_zero (ne_bot_of_coprime hM I.2.1) hB0 hprod.symm
  let F (p : ClassIdeals D c × CongruentUnits K M) : CongruenceCoset B M :=
    ⟨(p.2.1 : 𝓞 K) * g p.1, B.mul_mem_left _ (hgB p.1), by
      have h : (p.2.1 : 𝓞 K) * g p.1 - 1 =
          (p.2.1 : 𝓞 K) * (g p.1 - 1) + ((p.2.1 : 𝓞 K) - 1) := by ring
      rw [h]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hg1 p.1)) p.2.2⟩
  have hF (p : ClassIdeals D c × CongruentUnits K M) :
      (F p : 𝓞 K) = (p.2.1 : 𝓞 K) * g p.1 := rfl
  have hspanF (p : ClassIdeals D c × CongruentUnits K M) :
      Ideal.span {(F p : 𝓞 K)} = p.1.1 * B := by
    rw [hF p, Ideal.span_singleton_mul_left_unit p.2.1.isUnit, hg p.1]
  have hsurj : Function.Surjective F := by
    intro x
    obtain ⟨I, hIB⟩ := exists_ideal_for_coset_point hM D c B hB hB0 hc x
    have hass : Associated (g I) x.1 := by
      rw [← Ideal.span_singleton_eq_span_singleton, hg I, hIB]
    obtain ⟨u, hu⟩ := hass
    have hgu : g I * u - 1 ∈ Ideal.span {(M : 𝓞 K)} := by
      rw [hu]
      exact x.2.2
    have hu1 : (u : 𝓞 K) - 1 ∈ Ideal.span {(M : 𝓞 K)} := by
      have h : (u : 𝓞 K) - 1 = (g I * u - 1) - (g I - 1) * u := by ring
      rw [h]
      exact Ideal.sub_mem _ hgu (Ideal.mul_mem_right _ _ (hg1 I))
    refine ⟨(I, ⟨u, hu1⟩), Subtype.ext ?_⟩
    change (u : 𝓞 K) * g I = x.1
    exact (mul_comm _ _).trans hu
  exact ⟨Equiv.ofBijective F ⟨generatorMap_injective hB0 g hg0 F hF hspanF, hsurj⟩, hspanF⟩

end GlobalTheory.Mem.PartialZeta
