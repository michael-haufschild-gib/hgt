import GaloisForLFunctions.HTGeometry.HankelSecantCohenMacaulay
import GaloisForLFunctions.HTGeometry.KrullDimTrdeg
import GaloisForLFunctions.HTGeometry.ChainDegenerationCohenMacaulay
import GaloisForLFunctions.HTGeometry.RegularSequenceFreeness
import GaloisForLFunctions.HTGeometry.IntegralUnmixed
import GaloisForLFunctions.HTGeometry.HankelLeadingChart

/-!
# The Hankel secant ring is unmixed

Every associated prime of `A / aA` (`a ≠ 0`) has height one, for `A = K[x]/I_r`.

The ring carries a regular sequence `l_1, …, l_{2r}` of linear forms, and `A/(l)` has Krull
dimension `0`, hence is finite dimensional.  Monomials whose images form a basis of `A/(l)` are then
a basis of `A` over `B = K[y_1, …, y_{2r}]`, `y_j ↦ l_j` (`RegularSequenceFreeness`).  So `A` is
finite over the factorial ring `B`, the map `B → A` is injective, and relatively prime elements of
`B` stay a regular sequence on `A`; `height_eq_one_of_mem_associatedPrimes` applies.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

section List

variable {R : Type*} [CommRing R]

theorem isRegSeqMod_of_forall_isRegularOn : ∀ (rs : List R) (I : Ideal R),
    (∀ i (h : i < rs.length), IsRegularOn (I ⊔ Ideal.ofList (rs.take i)) rs[i]) →
    IsRegSeqMod I (fun j : Fin rs.length => rs[j])
  | [], _, _ => trivial
  | r :: rs, I, h => by
      refine ⟨fun x hx => ?_, ?_⟩
      · have h0 := h 0 (by simp)
        simp only [List.take_zero, ofList_nil, sup_bot_eq] at h0
        exact forall_mem_of_isRegularOn h0 x hx
      · refine isRegSeqMod_of_forall_isRegularOn rs (I ⊔ Ideal.span {r}) fun i hi => ?_
        have h1 := h (i + 1) (by simp; omega)
        simp only [List.take_succ_cons, ofList_cons, List.getElem_cons_succ] at h1
        rwa [sup_assoc]

theorem isRegSeqMod_of_isRegular (rs : List R) (I : Ideal R)
    (h : RingTheory.Sequence.IsRegular (R ⧸ I) rs) :
    IsRegSeqMod I (fun j : Fin rs.length => rs[j]) :=
  isRegSeqMod_of_forall_isRegularOn rs I fun i hi => isRegularOn_of_isRegular I rs h i hi

theorem span_range_getElem (rs : List R) :
    Ideal.span (Set.range fun j : Fin rs.length => rs[j]) = Ideal.ofList rs := by
  rw [Ideal.ofList]
  congr 1
  ext x
  simp only [Set.mem_range, Set.mem_setOf_eq, List.mem_iff_getElem]
  constructor
  · rintro ⟨j, rfl⟩; exact ⟨j, j.isLt, rfl⟩
  · rintro ⟨j, hj, rfl⟩; exact ⟨⟨j, hj⟩, rfl⟩

end List

theorem le_zero_of_add_le {x : WithBot ℕ∞} {n : ℕ} (h : x + (n : WithBot ℕ∞) ≤ n) : x ≤ 0 := by
  induction x using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe y =>
      induction y using ENat.recTopCoe with
      | top =>
          exfalso
          have h' : ((⊤ + (n : ℕ∞) : ℕ∞) : WithBot ℕ∞) ≤ ((n : ℕ∞) : WithBot ℕ∞) := by
            exact_mod_cast h
          rw [top_add, WithBot.coe_le_coe, top_le_iff] at h'
          exact ENat.coe_ne_top n h'
      | coe m =>
          have : ((m + n : ℕ) : WithBot ℕ∞) ≤ (n : ℕ) := by exact_mod_cast h
          have := WithBot.coe_le_coe.mp this
          have : m + n ≤ n := by exact_mod_cast this
          have hm : m = 0 := by omega
          rw [hm]; rfl

variable (K : Type) [Field K] [CharZero K]

/-- **The Hankel secant ring is unmixed.** -/
theorem height_eq_one_of_mem_associatedPrimes_hankel {N r : ℕ} (hN : 2 * r ≤ N)
    {a : HankelSecantRing K N r} (ha : a ≠ 0)
    {Q : Ideal (HankelSecantRing K N r)}
    (hQ : Q ∈ associatedPrimes (HankelSecantRing K N r)
      (HankelSecantRing K N r ⧸ Ideal.span {a})) :
    Q.height = 1 := by
  classical
  haveI : Infinite K := CharZero.infinite K
  set I := RHTower.finiteHankelSecantIdeal K N r with hIdef
  set A := HankelSecantRing K N r
  obtain ⟨rs, hlen, hhom, hreg⟩ := exists_homogeneous_isRegular_finiteHankelSecantIdeal K N r hN
  set d := rs.length
  set l : Fin d → MvPolynomial (Fin N) K := fun j => rs[j] with hldef
  have hl : ∀ j, (l j).IsHomogeneous 1 := fun j => hhom _ (List.getElem_mem _)
  have hregmod : IsRegSeqMod I l := isRegSeqMod_of_isRegular rs I hreg
  set J := I ⊔ Ideal.span (Set.range l) with hJdef
  have hJ : J = I ⊔ Ideal.ofList rs := by rw [hJdef, hldef, span_range_getElem]
  have hJtop : J ≠ ⊤ := by
    rw [hJ]
    intro htop
    exact hreg.2 ((Extra.smul_top_eq_top_iff I (Ideal.ofList rs)).mpr htop)
  -- `R/J` is finite dimensional
  have hdimJ : ringKrullDim (MvPolynomial (Fin N) K ⧸ J) ≤ 0 := by
    have hring := isRingRegularSeq_map_mk I rs hreg
    have h1 := ringKrullDim_quotient_ofList_add_length_le _ (rs.map (Ideal.Quotient.mk I)) rfl hring
    have h2 := ringKrullDim_hankelSecantQuotient_le K hN
    rw [List.length_map] at h1
    have h3 : ringKrullDim (A ⧸ Ideal.ofList (rs.map (Ideal.Quotient.mk I))) + (d : WithBot ℕ∞) ≤
        (d : ℕ) := by
      refine h1.trans (h2.trans ?_)
      rw [← hlen]; rfl
    have h4 := le_zero_of_add_le h3
    rw [ofList_map, ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotSup I _)] at h4
    rwa [hJ]
  haveI : Algebra.FiniteType K (MvPolynomial (Fin N) K ⧸ J) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K J) (Ideal.Quotient.mkₐ_surjective K J)
  haveI : Module.Finite K (MvPolynomial (Fin N) K ⧸ J) :=
    (Module.finite_iff_krullDimLE_zero K _).mpr (Ring.krullDimLE_iff.mpr (by exact_mod_cast hdimJ))
  -- a basis of `R/J` by monomials
  set T : Set (MvPolynomial (Fin N) K ⧸ J) :=
    Set.range fun m : Fin N →₀ ℕ => Ideal.Quotient.mk J (monomial m (1 : K)) with hT
  have hTspan : Submodule.span K T = ⊤ := by
    have : T = (Ideal.Quotient.mkₐ K J).toLinearMap '' Set.range (basisMonomials (Fin N) K) := by
      rw [hT, ← Set.range_comp, coe_basisMonomials]; rfl
    rw [this, Submodule.span_image, Module.Basis.span_eq, Submodule.map_top,
      LinearMap.range_eq_top]
    exact Ideal.Quotient.mkₐ_surjective K J
  obtain ⟨S, hST, hSspan, hSind⟩ := exists_linearIndependent K T
  haveI : Finite S := hSind.finite
  haveI : Fintype S := Fintype.ofFinite S
  have hmono : ∀ y : S, ∃ m : Fin N →₀ ℕ, Ideal.Quotient.mk J (monomial m (1 : K)) = y := by
    intro y; exact hST y.2
  choose m hm using hmono
  set e : S → MvPolynomial (Fin N) K := fun y => monomial (m y) 1 with hedef
  have he : ∀ y, (e y).IsHomogeneous (Finsupp.degree (m y)) := fun y =>
    isHomogeneous_monomial _ rfl
  have hind : LinearIndependent K (fun y => Ideal.Quotient.mk J (e y)) := by
    have : (fun y : S => Ideal.Quotient.mk J (e y)) = Subtype.val := funext fun y => hm y
    rw [this]; exact hSind
  have hspan : ∀ p, ∃ κ : S → K, p - ∑ y, κ y • e y ∈ J := by
    intro p
    have hp : Ideal.Quotient.mk J p ∈
        Submodule.span K (Set.range fun y : S => (y : MvPolynomial (Fin N) K ⧸ J)) := by
      rw [Subtype.range_coe_subtype, Set.setOf_mem_eq, hSspan, hTspan]; trivial
    obtain ⟨κ, hκ⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hp
    refine ⟨κ, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_sum, ← hκ, sub_eq_zero]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [show Ideal.Quotient.mk J (κ y • e y) = κ y • Ideal.Quotient.mk J (e y) from
      map_smul (Ideal.Quotient.mkₐ K J) (κ y) (e y), hm y]
  -- the polynomial subring `B = K[y]`
  set φ : MvPolynomial (Fin d) K →+* A := (Ideal.Quotient.mk I).comp (aeval l).toRingHom with hφ
  letI : Algebra (MvPolynomial (Fin d) K) A := φ.toAlgebra
  letI : Module (MvPolynomial (Fin d) K) A := Algebra.toModule
  have halg : ∀ c, algebraMap (MvPolynomial (Fin d) K) A c = Ideal.Quotient.mk I (aeval l c) :=
    fun c => rfl
  have hhomI : IsHomogIdeal I := isHomogIdeal_finiteHankelSecantIdeal K N r
  -- generation over `B`
  have hgen : ∀ x : A, ∃ b : S → MvPolynomial (Fin d) K,
      x = ∑ y, b y • (Ideal.Quotient.mk I (e y) : A) := by
    intro x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, hb⟩ := spannedMod_all hhomI hl _ he hspan p
    refine ⟨b, ?_⟩
    have h0 := Ideal.Quotient.eq_zero_iff_mem.mpr hb
    rw [map_sub, map_sum, sub_eq_zero] at h0
    rw [h0]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Algebra.smul_def, halg, map_mul]
  haveI : Module.Finite (MvPolynomial (Fin d) K) A := by
    refine ⟨⟨Finset.univ.image fun y => (Ideal.Quotient.mk I (e y) : A), ?_⟩⟩
    rw [eq_top_iff]
    intro x _
    obtain ⟨b, rfl⟩ := hgen x
    refine Submodule.sum_mem _ fun y _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    simp
  haveI : Algebra.IsIntegral (MvPolynomial (Fin d) K) A := Algebra.IsIntegral.of_finite _ _
  -- the subring is a polynomial ring
  have hS0 : Nonempty S := by
    by_contra hS
    rw [not_nonempty_iff, Set.isEmpty_coe_sort] at hS
    rw [hS, Submodule.span_empty, hTspan] at hSspan
    apply hJtop
    have hsub : Subsingleton (MvPolynomial (Fin N) K ⧸ J) :=
      (Submodule.subsingleton_iff K).mp (subsingleton_of_bot_eq_top hSspan)
    exact Ideal.Quotient.subsingleton_iff.mp hsub
  obtain ⟨y₀⟩ := hS0
  have hinj : Function.Injective (algebraMap (MvPolynomial (Fin d) K) A) := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    rw [halg, Ideal.Quotient.eq_zero_iff_mem] at hc
    have hb := eq_zero_of_sum_aeval_mul_mem I l hregmod e hind
      (fun y => if y = y₀ then c else 0) (by
        rw [Finset.sum_eq_single y₀ (fun y _ hy => by simp [hy]) (by simp), if_pos rfl]
        exact I.mul_mem_right _ hc)
    have := congrFun hb y₀
    simpa using this
  -- relatively prime elements stay regular
  have hcop : ∀ c c' : MvPolynomial (Fin d) K, IsRelPrime c c' → ∀ x : A,
      algebraMap _ A c' * x ∈ Ideal.span {algebraMap _ A c} →
        x ∈ Ideal.span {algebraMap _ A c} := by
    intro c c' hcc x hx
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    have key : ∀ z, (Ideal.Quotient.mk I z : A) ∈ Ideal.span {(Ideal.Quotient.mk I (aeval l c) : A)} ↔
        z ∈ I ⊔ Ideal.span {aeval l c} := by
      intro z
      rw [show Ideal.span {(Ideal.Quotient.mk I (aeval l c) : A)} =
          (Ideal.span {aeval l c}).map (Ideal.Quotient.mk I) by
        rw [Ideal.map_span, Set.image_singleton], Ideal.mem_quotient_iff_mem_sup, sup_comm]
    rw [halg, halg, ← map_mul, key] at hx
    rw [halg, key]
    exact mem_sup_span_of_isRelPrime hhomI hl hregmod _ he hind hspan hcc hx
  exact height_eq_one_of_mem_associatedPrimes hinj hcop ha hQ

end

end GaloisForLFunctions.HTGeometry
