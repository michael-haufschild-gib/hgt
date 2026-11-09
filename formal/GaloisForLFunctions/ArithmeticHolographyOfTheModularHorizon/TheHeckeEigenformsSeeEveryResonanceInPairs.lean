import GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon.TheHeckeOperatorIsSelfAdjoint
import GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon.TheMaassFormsSeeEveryResonanceInPairs
import GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon.OneCavityFunctionIsASharpReceiver

/-!
# The Hecke eigenforms see every resonance in pairs

Pairwise visibility (`exists_maass_pair_seeing`) produces two cuspidal Laplace eigenforms `v_l, v_i` with
`∫_𝒟 v_l v̄_i E*(ρ/2 − ½) ≠ 0`. Here the two eigenforms are made **Hecke eigenforms**, the arithmetic modes of the
cavity (`exists_hecke_pair_seeing`). B109 is solved by a cavity function built from Hecke eigenforms alone
(`exists_hecke_cavity_seeing_every_right_zero`), and one such function is a sharp receiver: its horocycle rate is
exactly the zero-free region of `ζ` (`exists_sharp_hecke_receiver`).

**Hecke eigenforms span every cusp space** (`span_heckeForms`). The cusp space `S(λ)` embeds into `L²(𝒟)` with
the Petersson product `⟨g, h⟩ = ∫_𝒟 ḡ h` (`inner_toImage`). On the image the Hecke operators are symmetric
(`HeckeAdjoint.integral_heckeH_mul_conj`) and commute (`HeckeCusp.heckeFamily_comm`), so the joint eigenspaces
span the finite-dimensional image (`iSup_jointEigenspace_eq_top`). A joint eigenvector pulls back to a cusp form
that is an eigenfunction of every `T_p` (`isHeckeForm_of_mem`). A finite spanning set is extracted by linear
independence (`exists_finite_heckeForms`).

**From eigenforms to Hecke eigenforms.** The pair entry `(u, v) ↦ ∫_𝒟 u v̄ E*` is additive and homogeneous in
`u`, conjugate-homogeneous in `v`, on cusp forms. If it vanished on all pairs of Hecke eigenforms, induction over
the spanning sets would make it vanish at `(v_l, v_i)` (`exists_pair_seeing_of_span`).
-/

open Complex MeasureTheory Set Filter Topology BoundedContinuousFunction
open scoped MatrixGroups UpperHalfPlane InnerProductSpace ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon

open _root_.RHTower GaloisForLFunctions.HTGeometry GaloisForLFunctions.BlackHoleRingdown
open GaloisForLFunctions.RHTower.DeckPointPair GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet
open GaloisForLFunctions.RHTower.Gamma0MaassHecke (heckeH)

/-- A **Hecke form** of eigenvalue `λ`: a cusp form of eigenvalue `λ` that is an eigenfunction of every `T_p`. -/
def IsHeckeForm (lam : ℝ) (g : ℍ → ℂ) : Prop :=
  g ∈ HeckeCusp.cuspSpace lam ∧ ∀ (p : ℕ) [Fact p.Prime], ∃ c : ℂ, heckeH p g = c • g

/-! ### Petersson symmetry on the cusp space -/

theorem integral_conj_heckeH_mul {lam : ℝ} {g h : ℍ → ℂ} (hg : g ∈ HeckeCusp.cuspSpace lam)
    (hh : h ∈ HeckeCusp.cuspSpace lam) (p : ℕ) [Fact p.Prime] :
    ∫ z in ModularGroup.fd, conj (heckeH p g z) * h z = ∫ z in ModularGroup.fd, conj (g z) * heckeH p h z := by
  have hs := HeckeAdjoint.integral_heckeH_mul_conj p (HeckeCusp.continuous_of_maass hh.2.1).measurable
    (HeckeCusp.continuous_of_maass hg.2.1).measurable (HeckeCusp.exists_bound hh) (HeckeCusp.exists_bound hg)
    hh.1 hg.1
  calc ∫ z in ModularGroup.fd, conj (heckeH p g z) * h z
        = ∫ z in ModularGroup.fd, h z * conj (heckeH p g z) := by congr 1; ext z; ring
    _ = ∫ z in ModularGroup.fd, heckeH p h z * conj (g z) := hs.symm
    _ = ∫ z in ModularGroup.fd, conj (g z) * heckeH p h z := by congr 1; ext z; ring

/-! ### The cusp space inside `L²` -/

/-- The `L²` class of a cusp form. -/
def toL2 (lam : ℝ) : HeckeCusp.cuspSpace lam →ₗ[ℂ] DeckL2 0 := (HeckeCusp.eigSpan lam).subtype ∘ₗ HeckeCusp.toSpan lam

theorem toL2_injective (lam : ℝ) : Function.Injective (toL2 lam) :=
  Subtype.val_injective.comp (HeckeCusp.toSpan_injective lam)

/-- The `L²` image of the cusp space `S(λ)`. -/
def L2Image (lam : ℝ) : Submodule ℂ (DeckL2 0) := LinearMap.range (toL2 lam)

/-- `S(λ)` is isomorphic to its `L²` image. -/
def toImage (lam : ℝ) : HeckeCusp.cuspSpace lam ≃ₗ[ℂ] L2Image lam :=
  LinearEquiv.ofInjective _ (toL2_injective lam)

instance (lam : ℝ) : FiniteDimensional ℂ (L2Image lam) := LinearEquiv.finiteDimensional (toImage lam)

/-- The `L²` product on `S(λ)` is the Petersson product. -/
theorem inner_toImage {lam : ℝ} (a b : HeckeCusp.cuspSpace lam) :
    ⟪toImage lam a, toImage lam b⟫_ℂ = ∫ z in ModularGroup.fd, conj ((a : ℍ → ℂ) z) * (b : ℍ → ℂ) z := by
  have ha : ((toImage lam a : L2Image lam) : DeckL2 0) =
      toDeckL2 (HeckeCusp.vecOf a.1) (HeckeCusp.memLp_vecOf a.2) := LinearEquiv.ofInjective_apply _ _
  have hb : ((toImage lam b : L2Image lam) : DeckL2 0) =
      toDeckL2 (HeckeCusp.vecOf b.1) (HeckeCusp.memLp_vecOf b.2) := LinearEquiv.ofInjective_apply _ _
  rw [Submodule.coe_inner, ha, hb]
  refine (inner_toDeckL2 (HeckeCusp.memLp_vecOf a.2) (HeckeCusp.memLp_vecOf b.2)).trans ?_
  refine setIntegral_congr_fun ModularGroup.isClosed_fd.measurableSet fun z _ => ?_
  exact inner_smul_ones _ _

/-- The Hecke family on the `L²` image. -/
def heckeImage (lam : ℝ) (n : ℕ) : Module.End ℂ (L2Image lam) := (toImage lam).conj (HeckeCusp.heckeFamily lam n)

theorem heckeImage_apply (lam : ℝ) (n : ℕ) (a : HeckeCusp.cuspSpace lam) :
    heckeImage lam n (toImage lam a) = toImage lam (HeckeCusp.heckeFamily lam n a) := by
  rw [heckeImage, LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]

theorem isSymmetric_heckeImage (lam : ℝ) (n : ℕ) :
    LinearMap.IsSymmetric (heckeImage lam n : L2Image lam →ₗ[ℂ] L2Image lam) := by
  intro x y
  obtain ⟨a, rfl⟩ := (toImage lam).surjective x
  obtain ⟨b, rfl⟩ := (toImage lam).surjective y
  rw [heckeImage_apply, heckeImage_apply, inner_toImage, inner_toImage]
  unfold HeckeCusp.heckeFamily
  split_ifs with hn
  · haveI := Fact.mk hn
    exact integral_conj_heckeH_mul a.2 b.2 n
  · rfl

theorem commute_heckeImage (lam : ℝ) (m n : ℕ) : Commute (heckeImage lam m) (heckeImage lam n) := by
  show heckeImage lam m * heckeImage lam n = heckeImage lam n * heckeImage lam m
  rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, heckeImage, heckeImage, ← LinearEquiv.conj_comp,
    ← LinearEquiv.conj_comp, HeckeCusp.heckeFamily_comm]

/-- **The joint Hecke eigenspaces span the cusp space.** -/
theorem iSup_jointEigenspace_eq_top (lam : ℝ) :
    ⨆ χ : ℕ → ℂ, ⨅ n, Module.End.eigenspace (heckeImage lam n) (χ n) = ⊤ :=
  LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute (isSymmetric_heckeImage lam)
    fun m n _ => commute_heckeImage lam m n

/-- A joint eigenvector is a Hecke form. -/
theorem isHeckeForm_of_mem {lam : ℝ} {χ : ℕ → ℂ} {x : L2Image lam}
    (hx : x ∈ ⨅ n, Module.End.eigenspace (heckeImage lam n) (χ n)) :
    IsHeckeForm lam ((toImage lam).symm x : ℍ → ℂ) := by
  refine ⟨((toImage lam).symm x).2, fun p hp => ⟨χ p, ?_⟩⟩
  have h := Module.End.mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 hx p)
  obtain ⟨a, rfl⟩ := (toImage lam).surjective x
  rw [heckeImage_apply, ← map_smul] at h
  have h2 := (toImage lam).injective h
  rw [LinearEquiv.symm_apply_apply]
  rw [HeckeCusp.heckeFamily, dif_pos hp.out] at h2
  exact congrArg Subtype.val h2

/-- **Hecke eigenforms span every cusp space.** -/
theorem span_heckeForms (lam : ℝ) :
    Submodule.span ℂ {g | IsHeckeForm lam g} = HeckeCusp.cuspSpace lam := by
  refine le_antisymm (Submodule.span_le.2 fun g hg => hg.1) fun g hg => ?_
  have hx : toImage lam ⟨g, hg⟩ ∈ ⨆ χ : ℕ → ℂ, ⨅ n, Module.End.eigenspace (heckeImage lam n) (χ n) := by
    rw [iSup_jointEigenspace_eq_top]; exact Submodule.mem_top
  have key := Submodule.iSup_induction _ (motive := fun x =>
      (((toImage lam).symm x : HeckeCusp.cuspSpace lam) : ℍ → ℂ) ∈ Submodule.span ℂ {g | IsHeckeForm lam g}) hx
    (fun χ x hx => Submodule.subset_span (isHeckeForm_of_mem hx))
    (by rw [LinearEquiv.map_zero, ZeroMemClass.coe_zero]; exact zero_mem _)
    (fun x y hx hy => by rw [LinearEquiv.map_add, Submodule.coe_add]; exact add_mem hx hy)
  rwa [LinearEquiv.symm_apply_apply] at key

/-- **A finite Hecke basis.** Finitely many Hecke forms span `S(λ)`. -/
theorem exists_finite_heckeForms (lam : ℝ) :
    ∃ S : Set (ℍ → ℂ), S.Finite ∧ (∀ g ∈ S, IsHeckeForm lam g) ∧ Submodule.span ℂ S = HeckeCusp.cuspSpace lam := by
  set t : Set (HeckeCusp.cuspSpace lam) := {a | IsHeckeForm lam a.1}
  obtain ⟨b, hbt, hspan, hli⟩ := exists_linearIndependent ℂ t
  have himg : Subtype.val '' t = {g | IsHeckeForm lam g} := by
    ext g
    exact ⟨fun ⟨a, ha, h⟩ => h ▸ ha, fun hg => ⟨⟨g, hg.1⟩, hg, rfl⟩⟩
  refine ⟨Subtype.val '' b, hli.setFinite.image _, fun _ ⟨a, ha, h⟩ => h ▸ hbt ha, ?_⟩
  have e1 := Submodule.span_image (HeckeCusp.cuspSpace lam).subtype (s := b)
  have e2 := Submodule.span_image (HeckeCusp.cuspSpace lam).subtype (s := t)
  rw [Submodule.coe_subtype] at e1 e2
  rw [e1, hspan, ← e2, himg, span_heckeForms]

/-! ### The pair entries are sesquilinear -/

theorem pairing_zero_left (s : ℂ) (h : ℍ → ℂ) : pairing s 0 h = 0 := by
  simp [pairing, pairIntegrand]

theorem pairing_zero_right (s : ℂ) (g : ℍ → ℂ) : pairing s g 0 = 0 := by
  simp [pairing, pairIntegrand]

theorem pairing_add_left {s : ℂ} {g g' h : ℍ → ℂ} (hi : IntegrableOn (pairIntegrand s g h) ModularGroup.fd)
    (hi' : IntegrableOn (pairIntegrand s g' h) ModularGroup.fd) :
    pairing s (g + g') h = pairing s g h + pairing s g' h := by
  unfold pairing
  rw [← integral_add hi hi']
  congr 1; ext z
  simp only [pairIntegrand, Pi.add_apply]; ring

theorem pairing_add_right {s : ℂ} {g h h' : ℍ → ℂ} (hi : IntegrableOn (pairIntegrand s g h) ModularGroup.fd)
    (hi' : IntegrableOn (pairIntegrand s g h') ModularGroup.fd) :
    pairing s g (h + h') = pairing s g h + pairing s g h' := by
  unfold pairing
  rw [← integral_add hi hi']
  congr 1; ext z
  simp only [pairIntegrand, Pi.add_apply, map_add]; ring

theorem pairing_smul_left (s c : ℂ) (g h : ℍ → ℂ) : pairing s (c • g) h = c * pairing s g h := by
  unfold pairing
  rw [← integral_const_mul]
  congr 1; ext z
  simp only [pairIntegrand, Pi.smul_apply, smul_eq_mul]; ring

theorem pairing_smul_right (s c : ℂ) (g h : ℍ → ℂ) : pairing s g (c • h) = conj c * pairing s g h := by
  unfold pairing
  rw [← integral_const_mul]
  congr 1; ext z
  simp only [pairIntegrand, Pi.smul_apply, smul_eq_mul, map_mul]; ring

/-! ### Pairwise visibility by spanning sets -/

/-- **Visibility passes to spanning sets.** If sets `S(λ)` of cusp forms span the cusp spaces, then at every
resonance `ρ/2`, `Re ρ > 0`, some pair from them has a nonzero pair entry. -/
theorem exists_pair_seeing_of_span {ρ : ℂ} (hζ : riemannZeta ρ = 0) (hpos : 0 < ρ.re) (S : ℝ → Set (ℍ → ℂ))
    (hS : ∀ lam, S lam ⊆ HeckeCusp.cuspSpace lam)
    (hspan : ∀ i : CuspEigenIndex 0, HeckeCusp.cuspSpace i.1 ≤ Submodule.span ℂ (S i.1)) :
    ∃ i l : CuspEigenIndex 0, ∃ u ∈ S l.1, ∃ v ∈ S i.1, pairing (ρ / 2) u v ≠ 0 := by
  obtain ⟨i, l, h⟩ := exists_maass_pair_seeing hζ hpos
  have hlt : ρ.re < 1 := lt_of_not_ge fun h => riemannZeta_ne_zero_of_one_le_re h hζ
  have hs0 : ρ / 2 ≠ 0 := fun h => by
    have : ρ = 0 := by linear_combination 2 * h
    rw [this] at hpos; simp at hpos
  have hs12 : ρ / 2 ≠ 1 / 2 := fun h => by
    have : ρ = 1 := by linear_combination 2 * h
    rw [this] at hlt; simp at hlt
  have hs1 : ρ / 2 ≠ 1 := fun h => by
    have : ρ = 2 := by linear_combination 2 * h
    rw [this] at hlt; norm_num at hlt
  by_contra hno
  push Not at hno
  -- the first slot
  have h1 : ∀ v ∈ S i.1, pairing (ρ / 2) (maassForm l) v = 0 := by
    intro v hv
    have hv' := hS _ hv
    exact (Submodule.span_induction
      (p := fun x _ => x ∈ HeckeCusp.cuspSpace l.1 ∧ pairing (ρ / 2) x v = 0)
      (fun x hx => ⟨hS _ hx, hno i l x hx v hv⟩) ⟨zero_mem _, pairing_zero_left _ _⟩
      (fun x y _ _ hx hy => ⟨add_mem hx.1 hy.1, by
        rw [pairing_add_left (integrableOn_pairIntegrand hx.1 hv' hs0 hs12 hs1)
          (integrableOn_pairIntegrand hy.1 hv' hs0 hs12 hs1), hx.2, hy.2, add_zero]⟩)
      (fun a x _ hx => ⟨Submodule.smul_mem _ a hx.1, by rw [pairing_smul_left, hx.2, mul_zero]⟩)
      (hspan l (maassForm_mem l))).2
  -- the second slot
  exact h (Submodule.span_induction
    (p := fun x _ => x ∈ HeckeCusp.cuspSpace i.1 ∧ pairing (ρ / 2) (maassForm l) x = 0)
    (fun x hx => ⟨hS _ hx, h1 x hx⟩) ⟨zero_mem _, pairing_zero_right _ _⟩
    (fun x y _ _ hx hy => ⟨add_mem hx.1 hy.1, by
      rw [pairing_add_right (integrableOn_pairIntegrand (maassForm_mem l) hx.1 hs0 hs12 hs1)
        (integrableOn_pairIntegrand (maassForm_mem l) hy.1 hs0 hs12 hs1), hx.2, hy.2, add_zero]⟩)
    (fun a x _ hx => ⟨Submodule.smul_mem _ a hx.1, by rw [pairing_smul_right, hx.2, mul_zero]⟩)
    (hspan i (maassForm_mem i))).2

/-- **Hecke eigenforms see every resonance in pairs.** For every zero `ρ` of `ζ` with `Re ρ > 0` there are
Hecke–Maass forms `u, v` with `∫_𝒟 u v̄ E*(ρ/2 − ½) ≠ 0`. -/
theorem exists_hecke_pair_seeing {ρ : ℂ} (hζ : riemannZeta ρ = 0) (hpos : 0 < ρ.re) :
    ∃ (lam₁ lam₂ : ℝ) (u v : ℍ → ℂ), IsHeckeForm lam₁ u ∧ IsHeckeForm lam₂ v ∧ pairing (ρ / 2) u v ≠ 0 := by
  obtain ⟨i, l, u, hu, v, hv, h⟩ := exists_pair_seeing_of_span hζ hpos (fun lam => {g | IsHeckeForm lam g})
    (fun _ _ hg => hg.1) fun i => (span_heckeForms i.1).ge
  exact ⟨l.1, i.1, u, v, hu, hv, h⟩

/-! ### B109 for Hecke eigenforms -/

/-- A finite Hecke basis of `S(λ)`. -/
def heckeBasis (lam : ℝ) : Set (ℍ → ℂ) := (exists_finite_heckeForms lam).choose

theorem heckeBasis_finite (lam : ℝ) : (heckeBasis lam).Finite := (exists_finite_heckeForms lam).choose_spec.1

theorem isHeckeForm_of_mem_heckeBasis {lam : ℝ} {g : ℍ → ℂ} (hg : g ∈ heckeBasis lam) : IsHeckeForm lam g :=
  (exists_finite_heckeForms lam).choose_spec.2.1 g hg

theorem span_heckeBasis (lam : ℝ) : Submodule.span ℂ (heckeBasis lam) = HeckeCusp.cuspSpace lam :=
  (exists_finite_heckeForms lam).choose_spec.2.2

/-- The Hecke basis forms of all cuspidal eigenvalues. -/
def HeckeIndex : Type := Σ i : CuspEigenIndex 0, heckeBasis i.1

instance : Countable HeckeIndex := by
  haveI := countable_cuspEigenIndex
  haveI : ∀ i : CuspEigenIndex 0, Finite (heckeBasis i.1) := fun i => (heckeBasis_finite _).to_subtype
  unfold HeckeIndex
  infer_instance

instance : Nonempty HeckeIndex := by
  haveI : Nonempty (CuspEigenIndex 0) := by haveI := infinite_cuspEigenIndex; infer_instance
  obtain ⟨i⟩ := ‹Nonempty (CuspEigenIndex 0)›
  obtain ⟨g, hg⟩ : (heckeBasis i.1).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have := span_heckeBasis i.1
    rw [h, Submodule.span_empty] at this
    exact HeckeCusp.cuspSpace_ne_bot i this.symm
  exact ⟨⟨i, g, hg⟩⟩

/-- An enumeration of the Hecke basis forms. -/
def heckeEnum : ℕ → HeckeIndex := (exists_surjective_nat HeckeIndex).choose

theorem heckeEnum_surjective : Function.Surjective heckeEnum := (exists_surjective_nat HeckeIndex).choose_spec

/-- The `n`-th Hecke basis form. -/
def heckeV (n : ℕ) : ℍ → ℂ := ((heckeEnum n).2 : ℍ → ℂ)

/-- Its eigenvalue. -/
def heckeLam (n : ℕ) : ℝ := (heckeEnum n).1.1

theorem isHeckeForm_heckeV (n : ℕ) : IsHeckeForm (heckeLam n) (heckeV n) :=
  isHeckeForm_of_mem_heckeBasis (heckeEnum n).2.2

theorem heckeV_mem (n : ℕ) : heckeV n ∈ HeckeCusp.cuspSpace (heckeLam n) := (isHeckeForm_heckeV n).1

/-- **The enumerated Hecke basis sees every resonance in pairs.** -/
theorem exists_heckeV_pair_seeing {ρ : ℂ} (hζ : riemannZeta ρ = 0) (hpos : 0 < ρ.re) :
    ∃ n m : ℕ, pairing (ρ / 2) (heckeV n) (heckeV m) ≠ 0 := by
  obtain ⟨i, l, u, hu, v, hv', h⟩ := exists_pair_seeing_of_span hζ hpos heckeBasis
    (fun _ _ hg => (isHeckeForm_of_mem_heckeBasis hg).1) fun i => (span_heckeBasis i.1).ge
  obtain ⟨n, hn⟩ := heckeEnum_surjective ⟨l, u, hu⟩
  obtain ⟨m, hm⟩ := heckeEnum_surjective ⟨i, v, hv'⟩
  refine ⟨n, m, ?_⟩
  show pairing (ρ / 2) ((heckeEnum n).2 : ℍ → ℂ) ((heckeEnum m).2 : ℍ → ℂ) ≠ 0
  rw [hn, hm]
  exact h

/-- **B109 for Hecke eigenforms.** There are normalizers `M_n > 0` and one cuspidal cavity function
`g = Σ_n x_n 2^{−n} v_n/M_n` of Hecke–Maass forms `v_n` whose energy sees every right resonance; a horocycle rate
`y^α` of `|g|²` forces `Re ρ ≤ 2 − 2α` at every zero `ρ` of `ζ` with `Re ρ > ½`. -/
theorem exists_hecke_cavity_seeing_every_right_zero :
    ∃ (v : ℕ → ℍ → ℂ) (lam : ℕ → ℝ) (M : ℕ → ℝ), (∀ n, IsHeckeForm (lam n) (v n)) ∧
      (∀ n, 0 < M n) ∧ ∃ x : ℕ →ᵇ ℂ, (∀ y : ℝ, 0 < y → response (cavity (cuspFamily v M) x) y = 0) ∧
        (∀ ρ : ℂ, riemannZeta ρ = 0 → 1 / 2 < ρ.re →
          seedTransform (fun z => ((‖cavity (cuspFamily v M) x z‖ ^ 2 : ℝ) : ℂ)) (ρ / 2) ≠ 0) ∧
        ∀ (α : ℝ) (c : ℂ) (C : ℝ), (∀ y : ℝ, 0 < y → y ≤ 1 →
          ‖response (fun z => ((‖cavity (cuspFamily v M) x z‖ ^ 2 : ℝ) : ℂ)) y - c‖ ≤ C * y ^ α) →
          ∀ ρ : ℂ, riemannZeta ρ = 0 → 1 / 2 < ρ.re → ρ.re ≤ 2 - 2 * α := by
  obtain ⟨M, hM, hu, hiff⟩ := cuspFunction_sees_every_right_zero_iff (v := heckeV) (lam := heckeLam) heckeV_mem
  obtain ⟨x, hx⟩ := hiff.2 fun ρ hζ hρ => exists_heckeV_pair_seeing hζ (by linarith)
  have hMb : ∀ n, 0 < M n ∧ ∀ z : ℍ, ‖heckeV n z‖ ≤ M n * Real.exp (-Real.pi * z.im) := fun n =>
    ⟨hM n, fun z => by
      have := hu.envelope n z
      simp only [cuspFamily, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (hM n).le] at this
      rwa [inv_mul_le_iff₀ (hM n)] at this⟩
  exact ⟨heckeV, heckeLam, M, isHeckeForm_heckeV, hM, x,
    fun y hy => response_cavity_cuspFamily_eq_zero heckeV_mem hMb x hy, hx,
    fun α c C hrate ρ hζ hρ => re_le_of_cavity_rate hu hx hrate hζ hρ⟩

/-- **One Hecke cavity function is a sharp receiver.** There are Hecke–Maass forms `v_n`, normalizers `M_n > 0` and
coefficients `x` such that `g = Σ_n x_n 2^{−n} v_n/M_n` is cuspidal and: RH holds iff `|g|²` converges on closed
horocycles at rate `y^{3/4−ε}` for every `ε > 0`; `ζ` has a zero-free strip iff `|g|²` converges at some rate
`y^α`, `α > ½`. -/
theorem exists_sharp_hecke_receiver :
    ∃ (v : ℕ → ℍ → ℂ) (lam : ℕ → ℝ) (M : ℕ → ℝ) (x : ℕ →ᵇ ℂ),
      (∀ n, IsHeckeForm (lam n) (v n)) ∧ (∀ n, 0 < M n) ∧
      (∀ y : ℝ, 0 < y → response (cavity (cuspFamily v M) x) y = 0) ∧
      (RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∃ (c : ℂ) (C : ℝ), ∀ y : ℝ, 0 < y → y ≤ 1 →
        ‖response (fun z => ((‖cavity (cuspFamily v M) x z‖ ^ 2 : ℝ) : ℂ)) y - c‖ ≤ C * y ^ (3 / 4 - ε)) ∧
      ((∃ δ : ℝ, 0 < δ ∧ ∀ z : ℂ, 1 - δ < z.re → riemannZeta z ≠ 0) ↔
        ∃ α : ℝ, 1 / 2 < α ∧ ∃ (c : ℂ) (C : ℝ), ∀ y : ℝ, 0 < y → y ≤ 1 →
          ‖response (fun z => ((‖cavity (cuspFamily v M) x z‖ ^ 2 : ℝ) : ℂ)) y - c‖ ≤ C * y ^ α) := by
  obtain ⟨x, hM, h0, hRH, hstrip⟩ := sharp_receiver_of_pairs heckeV_mem fun ρ hζ hρ =>
    exists_heckeV_pair_seeing hζ (by linarith)
  exact ⟨heckeV, heckeLam, normM heckeV_mem, x, isHeckeForm_heckeV, hM, h0, hRH, hstrip⟩

end GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon
