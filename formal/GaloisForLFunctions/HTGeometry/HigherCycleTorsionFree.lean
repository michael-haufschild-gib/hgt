import GaloisForLFunctions.HTGeometry.StanleyReisnerCycleClasses

/-!
# Higher cycle classes are torsion-free (C₅ Tor₃, C₆ Tor₄)

Extending the degree-2 module structure (`C4KoszulTorModule`) up the reduced-cohomology tower, over a
field a nonzero scalar multiple of the pentagon (`C₅`, `Tor₃`) or hexagon (`C₆`, `Tor₄`) Koszul cycle is
still not a boundary — so each class is torsion-free (its `F`-span is free rank one), reusing the done
non-boundary results `srPentTriple_thirdKoszulHomology_nonzero` / `srHexTuple_fourthKoszulHomology_nonzero`
together with the `F`-linearity of the differential and the scaling-closure of the alternating tensors.
-/

namespace GaloisForLFunctions.HTGeometry

variable {R α : Type*} [CommRing R] [DecidableEq α] [Fintype α]

omit [DecidableEq α] [Fintype α] in
/-- Scaling an alternating `4`-tensor stays alternating. -/
theorem IsAlternating4_smul {M : Type*} [AddCommGroup M] [Module R M] {b : α → α → α → α → M}
    (hb : IsAlternating4 b) (r : R) : IsAlternating4 (fun i j k l => r • b i j k l) where
  antisym12 i j k l := by rw [hb.antisym12 i j k l, smul_neg]
  antisym23 i j k l := by rw [hb.antisym23 i j k l, smul_neg]
  antisym34 i j k l := by rw [hb.antisym34 i j k l, smul_neg]
  alt i j k l h := by rw [hb.alt i j k l h, smul_zero]

omit [DecidableEq α] [Fintype α] in
/-- Scaling an alternating `5`-tensor stays alternating. -/
theorem IsAlternating5_smul {M : Type*} [AddCommGroup M] [Module R M] {b : α → α → α → α → α → M}
    (hb : IsAlternating5 b) (r : R) : IsAlternating5 (fun i j k l m => r • b i j k l m) where
  antisym12 i j k l m := by rw [hb.antisym12 i j k l m, smul_neg]
  antisym23 i j k l m := by rw [hb.antisym23 i j k l m, smul_neg]
  antisym34 i j k l m := by rw [hb.antisym34 i j k l m, smul_neg]
  antisym45 i j k l m := by rw [hb.antisym45 i j k l m, smul_neg]
  alt i j k l m h := by rw [hb.alt i j k l m h, smul_zero]

omit [DecidableEq α] in
/-- The fourth Koszul differential is `R`-linear in its `4`-tensor. -/
theorem srKoszulBoundary4_smul (facets : Finset (Finset α)) (r : R)
    (b : α → α → α → α → stanleyReisnerRing R facets) :
    srKoszulBoundary4 facets (fun i j k l => r • b i j k l)
      = fun i j k => r • srKoszulBoundary4 facets b i j k := by
  funext i j k
  simp only [srKoszulBoundary4, Finset.smul_sum]
  exact Finset.sum_congr rfl (fun l _ => by rw [smul_mul_assoc])

omit [DecidableEq α] in
/-- The fifth Koszul differential is `R`-linear in its `5`-tensor. -/
theorem srKoszulBoundary5_smul (facets : Finset (Finset α)) (r : R)
    (b : α → α → α → α → α → stanleyReisnerRing R facets) :
    srKoszulBoundary5 facets (fun i j k l m => r • b i j k l m)
      = fun i j k l => r • srKoszulBoundary5 facets b i j k l := by
  funext i j k l
  simp only [srKoszulBoundary5, Finset.smul_sum]
  exact Finset.sum_congr rfl (fun m _ => by rw [smul_mul_assoc])

/-- **`C₅` `Tor₃` class is torsion-free.**  Over a field, a nonzero scalar multiple of the pentagon
Koszul cycle is not a fourth Koszul boundary. -/
theorem srPentTripleCycle_smul_not_koszulBoundary4 (F : Type*) [Field F] (facets : Finset (Finset α))
    {a b c d e : α} (hab : a ≠ b) (hbc : b ≠ c) (hcd : c ≠ d) (hde : d ≠ e) (hea : e ≠ a)
    (hac : a ≠ c) (hbd : b ≠ d) (hce : c ≠ e)
    (ha : IsFaceOf (↑facets : Set (Finset α)) {a}) (hb : IsFaceOf (↑facets : Set (Finset α)) {b})
    (hc : IsFaceOf (↑facets : Set (Finset α)) {c}) (hd : IsFaceOf (↑facets : Set (Finset α)) {d})
    (he : IsFaceOf (↑facets : Set (Finset α)) {e})
    (hab_f : IsFaceOf (↑facets : Set (Finset α)) {a, b})
    (hbc_f : IsFaceOf (↑facets : Set (Finset α)) {b, c})
    (hcd_f : IsFaceOf (↑facets : Set (Finset α)) {c, d})
    (hde_f : IsFaceOf (↑facets : Set (Finset α)) {d, e})
    (hea_f : IsFaceOf (↑facets : Set (Finset α)) {e, a})
    (hce_nf : ¬ IsFaceOf (↑facets : Set (Finset α)) {c, e}) {r : F} (hr : r ≠ 0) :
    ¬ ∃ b4 : α → α → α → α → stanleyReisnerRing F facets,
      IsAlternating4 b4 ∧ srKoszulBoundary4 facets b4 = r • srPentTripleCycle F facets a b c d e := by
  rintro ⟨b4, halt, heq⟩
  refine (srPentTriple_thirdKoszulHomology_nonzero facets hab hbc hcd hde hea hac hbd hce
    ha hb hc hd he hab_f hbc_f hcd_f hde_f hea_f hce_nf).2
    ⟨fun i j k l => r⁻¹ • b4 i j k l, IsAlternating4_smul halt r⁻¹, ?_⟩
  rw [srKoszulBoundary4_smul, heq]
  funext i j k
  simp only [Pi.smul_apply, smul_smul, inv_mul_cancel₀ hr, one_smul]

/-- **`C₆` `Tor₄` class is torsion-free.**  Over a field, a nonzero scalar multiple of the hexagon
Koszul cycle is not a fifth Koszul boundary. -/
theorem srHexTupleCycle_smul_not_koszulBoundary5 (F : Type*) [Field F] (facets : Finset (Finset α))
    {a b c d e f : α} (hab : a ≠ b) (hbc : b ≠ c) (hcd : c ≠ d) (hde : d ≠ e) (hef : e ≠ f)
    (hfa : f ≠ a) (hac : a ≠ c) (hbd : b ≠ d) (hce : c ≠ e) (hdf : d ≠ f)
    (ha : IsFaceOf (↑facets : Set (Finset α)) {a}) (hb : IsFaceOf (↑facets : Set (Finset α)) {b})
    (hc : IsFaceOf (↑facets : Set (Finset α)) {c}) (hd : IsFaceOf (↑facets : Set (Finset α)) {d})
    (he : IsFaceOf (↑facets : Set (Finset α)) {e}) (hf : IsFaceOf (↑facets : Set (Finset α)) {f})
    (hab_f : IsFaceOf (↑facets : Set (Finset α)) {a, b})
    (hbc_f : IsFaceOf (↑facets : Set (Finset α)) {b, c})
    (hcd_f : IsFaceOf (↑facets : Set (Finset α)) {c, d})
    (hde_f : IsFaceOf (↑facets : Set (Finset α)) {d, e})
    (hef_f : IsFaceOf (↑facets : Set (Finset α)) {e, f})
    (hfa_f : IsFaceOf (↑facets : Set (Finset α)) {f, a})
    (hdf_nf : ¬ IsFaceOf (↑facets : Set (Finset α)) {d, f}) {r : F} (hr : r ≠ 0) :
    ¬ ∃ b5 : α → α → α → α → α → stanleyReisnerRing F facets,
      IsAlternating5 b5 ∧ srKoszulBoundary5 facets b5 = r • srHexTupleCycle F facets a b c d e f := by
  rintro ⟨b5, halt, heq⟩
  refine (srHexTuple_fourthKoszulHomology_nonzero facets hab hbc hcd hde hef hfa hac hbd hce hdf
    ha hb hc hd he hf hab_f hbc_f hcd_f hde_f hef_f hfa_f hdf_nf).2
    ⟨fun i j k l m => r⁻¹ • b5 i j k l m, IsAlternating5_smul halt r⁻¹, ?_⟩
  rw [srKoszulBoundary5_smul, heq]
  funext i j k l
  simp only [Pi.smul_apply, smul_smul, inv_mul_cancel₀ hr, one_smul]

/-! ## C₅ Tor₃ as a module class -/

omit [DecidableEq α] [Fintype α] in
/-- Sum of alternating `4`-tensors stays alternating. -/
theorem IsAlternating4_add {M : Type*} [AddCommGroup M] {b b' : α → α → α → α → M}
    (hb : IsAlternating4 b) (hb' : IsAlternating4 b') :
    IsAlternating4 (fun i j k l => b i j k l + b' i j k l) where
  antisym12 i j k l := by rw [hb.antisym12 i j k l, hb'.antisym12 i j k l, neg_add]
  antisym23 i j k l := by rw [hb.antisym23 i j k l, hb'.antisym23 i j k l, neg_add]
  antisym34 i j k l := by rw [hb.antisym34 i j k l, hb'.antisym34 i j k l, neg_add]
  alt i j k l h := by rw [hb.alt i j k l h, hb'.alt i j k l h, add_zero]

omit [DecidableEq α] [Fintype α] in
/-- The zero `4`-tensor is alternating. -/
theorem IsAlternating4_zero {M : Type*} [AddCommGroup M] :
    IsAlternating4 (0 : α → α → α → α → M) where
  antisym12 i j k l := by simp
  antisym23 i j k l := by simp
  antisym34 i j k l := by simp
  alt i j k l h := by simp

/-- The submodule of alternating `4`-tensors over the Stanley–Reisner ring. -/
def alternating4Submodule (R : Type*) [CommRing R] (facets : Finset (Finset α)) :
    Submodule R (α → α → α → α → stanleyReisnerRing R facets) where
  carrier := {b | IsAlternating4 b}
  add_mem' hb hb' := IsAlternating4_add hb hb'
  zero_mem' := IsAlternating4_zero
  smul_mem' r _ hb := IsAlternating4_smul hb r

/-- The fourth Koszul differential as an `R`-linear map. -/
noncomputable def srKoszulBoundary4ₗ (R : Type*) [CommRing R] (facets : Finset (Finset α)) :
    (α → α → α → α → stanleyReisnerRing R facets) →ₗ[R]
      (α → α → α → stanleyReisnerRing R facets) where
  toFun b := srKoszulBoundary4 facets b
  map_add' b b' := by
    funext i j k
    simp only [srKoszulBoundary4, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun l _ => by ring)
  map_smul' r b := by
    funext i j k
    simp only [srKoszulBoundary4, Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
    exact Finset.sum_congr rfl (fun l _ => by rw [smul_mul_assoc])

/-- The degree-3 Koszul boundaries: `d₄` of alternating `4`-tensors. -/
noncomputable def srPentTripleBoundaries (R : Type*) [CommRing R] (facets : Finset (Finset α)) :
    Submodule R (α → α → α → stanleyReisnerRing R facets) :=
  Submodule.map (srKoszulBoundary4ₗ R facets) (alternating4Submodule R facets)

/-- The `C₅` third Koszul homology class in `(α → α → α → S) ⧸ (d₄-boundaries)`. -/
noncomputable def srPentTripleTorClass (R : Type*) [CommRing R] (facets : Finset (Finset α))
    (a b c d e : α) :
    (α → α → α → stanleyReisnerRing R facets) ⧸ srPentTripleBoundaries R facets :=
  Submodule.Quotient.mk (srPentTripleCycle R facets a b c d e)

/-- The `C₅` `Tor₃` class is nonzero — the pentagon cycle is not a `d₄`-boundary. -/
theorem srPentTripleTorClass_ne_zero (F : Type*) [Field F] (facets : Finset (Finset α))
    {a b c d e : α} (hab : a ≠ b) (hbc : b ≠ c) (hcd : c ≠ d) (hde : d ≠ e) (hea : e ≠ a)
    (hac : a ≠ c) (hbd : b ≠ d) (hce : c ≠ e)
    (ha : IsFaceOf (↑facets : Set (Finset α)) {a}) (hb : IsFaceOf (↑facets : Set (Finset α)) {b})
    (hc : IsFaceOf (↑facets : Set (Finset α)) {c}) (hd : IsFaceOf (↑facets : Set (Finset α)) {d})
    (he : IsFaceOf (↑facets : Set (Finset α)) {e})
    (hab_f : IsFaceOf (↑facets : Set (Finset α)) {a, b})
    (hbc_f : IsFaceOf (↑facets : Set (Finset α)) {b, c})
    (hcd_f : IsFaceOf (↑facets : Set (Finset α)) {c, d})
    (hde_f : IsFaceOf (↑facets : Set (Finset α)) {d, e})
    (hea_f : IsFaceOf (↑facets : Set (Finset α)) {e, a})
    (hce_nf : ¬ IsFaceOf (↑facets : Set (Finset α)) {c, e}) :
    srPentTripleTorClass F facets a b c d e ≠ 0 := by
  intro h
  have hmem : srPentTripleCycle F facets a b c d e ∈ srPentTripleBoundaries F facets :=
    (Submodule.Quotient.mk_eq_zero _).mp h
  obtain ⟨b4, hb4mem, hb4eq⟩ := Submodule.mem_map.mp hmem
  exact (srPentTriple_thirdKoszulHomology_nonzero facets hab hbc hcd hde hea hac hbd hce
    ha hb hc hd he hab_f hbc_f hcd_f hde_f hea_f hce_nf).2 ⟨b4, hb4mem, hb4eq⟩

/-- **`C₅` `Tor₃` embedding.**  The pentagon `Tor₃` class spans a free rank-one `F`-line. -/
noncomputable def srPentTripleTorEquiv (F : Type*) [Field F] (facets : Finset (Finset α))
    {a b c d e : α} (hab : a ≠ b) (hbc : b ≠ c) (hcd : c ≠ d) (hde : d ≠ e) (hea : e ≠ a)
    (hac : a ≠ c) (hbd : b ≠ d) (hce : c ≠ e)
    (ha : IsFaceOf (↑facets : Set (Finset α)) {a}) (hb : IsFaceOf (↑facets : Set (Finset α)) {b})
    (hc : IsFaceOf (↑facets : Set (Finset α)) {c}) (hd : IsFaceOf (↑facets : Set (Finset α)) {d})
    (he : IsFaceOf (↑facets : Set (Finset α)) {e})
    (hab_f : IsFaceOf (↑facets : Set (Finset α)) {a, b})
    (hbc_f : IsFaceOf (↑facets : Set (Finset α)) {b, c})
    (hcd_f : IsFaceOf (↑facets : Set (Finset α)) {c, d})
    (hde_f : IsFaceOf (↑facets : Set (Finset α)) {d, e})
    (hea_f : IsFaceOf (↑facets : Set (Finset α)) {e, a})
    (hce_nf : ¬ IsFaceOf (↑facets : Set (Finset α)) {c, e}) :
    F ≃ₗ[F] ↥(F ∙ srPentTripleTorClass F facets a b c d e) :=
  LinearEquiv.toSpanNonzeroSingleton F _ (srPentTripleTorClass F facets a b c d e)
    (srPentTripleTorClass_ne_zero F facets hab hbc hcd hde hea hac hbd hce ha hb hc hd he
      hab_f hbc_f hcd_f hde_f hea_f hce_nf)

/-! ## C₆ Tor₄ as a module class -/

omit [DecidableEq α] [Fintype α] in
/-- Sum of alternating `5`-tensors stays alternating. -/
theorem IsAlternating5_add {M : Type*} [AddCommGroup M] {b b' : α → α → α → α → α → M}
    (hb : IsAlternating5 b) (hb' : IsAlternating5 b') :
    IsAlternating5 (fun i j k l m => b i j k l m + b' i j k l m) where
  antisym12 i j k l m := by rw [hb.antisym12 i j k l m, hb'.antisym12 i j k l m, neg_add]
  antisym23 i j k l m := by rw [hb.antisym23 i j k l m, hb'.antisym23 i j k l m, neg_add]
  antisym34 i j k l m := by rw [hb.antisym34 i j k l m, hb'.antisym34 i j k l m, neg_add]
  antisym45 i j k l m := by rw [hb.antisym45 i j k l m, hb'.antisym45 i j k l m, neg_add]
  alt i j k l m h := by rw [hb.alt i j k l m h, hb'.alt i j k l m h, add_zero]

omit [DecidableEq α] [Fintype α] in
/-- The zero `5`-tensor is alternating. -/
theorem IsAlternating5_zero {M : Type*} [AddCommGroup M] :
    IsAlternating5 (0 : α → α → α → α → α → M) where
  antisym12 i j k l m := by simp
  antisym23 i j k l m := by simp
  antisym34 i j k l m := by simp
  antisym45 i j k l m := by simp
  alt i j k l m h := by simp

/-- The submodule of alternating `5`-tensors over the Stanley–Reisner ring. -/
def alternating5Submodule (R : Type*) [CommRing R] (facets : Finset (Finset α)) :
    Submodule R (α → α → α → α → α → stanleyReisnerRing R facets) where
  carrier := {b | IsAlternating5 b}
  add_mem' hb hb' := IsAlternating5_add hb hb'
  zero_mem' := IsAlternating5_zero
  smul_mem' r _ hb := IsAlternating5_smul hb r

/-- The fifth Koszul differential as an `R`-linear map. -/
noncomputable def srKoszulBoundary5ₗ (R : Type*) [CommRing R] (facets : Finset (Finset α)) :
    (α → α → α → α → α → stanleyReisnerRing R facets) →ₗ[R]
      (α → α → α → α → stanleyReisnerRing R facets) where
  toFun b := srKoszulBoundary5 facets b
  map_add' b b' := by
    funext i j k l
    simp only [srKoszulBoundary5, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun m _ => by ring)
  map_smul' r b := by
    funext i j k l
    simp only [srKoszulBoundary5, Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
    exact Finset.sum_congr rfl (fun m _ => by rw [smul_mul_assoc])

/-- The degree-4 Koszul boundaries: `d₅` of alternating `5`-tensors. -/
noncomputable def srHexTupleBoundaries (R : Type*) [CommRing R] (facets : Finset (Finset α)) :
    Submodule R (α → α → α → α → stanleyReisnerRing R facets) :=
  Submodule.map (srKoszulBoundary5ₗ R facets) (alternating5Submodule R facets)

/-- The `C₆` fourth Koszul homology class in `(α → α → α → α → S) ⧸ (d₅-boundaries)`. -/
noncomputable def srHexTupleTorClass (R : Type*) [CommRing R] (facets : Finset (Finset α))
    (a b c d e f : α) :
    (α → α → α → α → stanleyReisnerRing R facets) ⧸ srHexTupleBoundaries R facets :=
  Submodule.Quotient.mk (srHexTupleCycle R facets a b c d e f)

/-- The `C₆` `Tor₄` class is nonzero — the hexagon cycle is not a `d₅`-boundary. -/
theorem srHexTupleTorClass_ne_zero (F : Type*) [Field F] (facets : Finset (Finset α))
    {a b c d e f : α} (hab : a ≠ b) (hbc : b ≠ c) (hcd : c ≠ d) (hde : d ≠ e) (hef : e ≠ f)
    (hfa : f ≠ a) (hac : a ≠ c) (hbd : b ≠ d) (hce : c ≠ e) (hdf : d ≠ f)
    (ha : IsFaceOf (↑facets : Set (Finset α)) {a}) (hb : IsFaceOf (↑facets : Set (Finset α)) {b})
    (hc : IsFaceOf (↑facets : Set (Finset α)) {c}) (hd : IsFaceOf (↑facets : Set (Finset α)) {d})
    (he : IsFaceOf (↑facets : Set (Finset α)) {e}) (hf : IsFaceOf (↑facets : Set (Finset α)) {f})
    (hab_f : IsFaceOf (↑facets : Set (Finset α)) {a, b})
    (hbc_f : IsFaceOf (↑facets : Set (Finset α)) {b, c})
    (hcd_f : IsFaceOf (↑facets : Set (Finset α)) {c, d})
    (hde_f : IsFaceOf (↑facets : Set (Finset α)) {d, e})
    (hef_f : IsFaceOf (↑facets : Set (Finset α)) {e, f})
    (hfa_f : IsFaceOf (↑facets : Set (Finset α)) {f, a})
    (hdf_nf : ¬ IsFaceOf (↑facets : Set (Finset α)) {d, f}) :
    srHexTupleTorClass F facets a b c d e f ≠ 0 := by
  intro h
  have hmem : srHexTupleCycle F facets a b c d e f ∈ srHexTupleBoundaries F facets :=
    (Submodule.Quotient.mk_eq_zero _).mp h
  obtain ⟨b5, hb5mem, hb5eq⟩ := Submodule.mem_map.mp hmem
  exact (srHexTuple_fourthKoszulHomology_nonzero facets hab hbc hcd hde hef hfa hac hbd hce hdf
    ha hb hc hd he hf hab_f hbc_f hcd_f hde_f hef_f hfa_f hdf_nf).2 ⟨b5, hb5mem, hb5eq⟩

/-- **`C₆` `Tor₄` embedding.**  The hexagon `Tor₄` class spans a free rank-one `F`-line. -/
noncomputable def srHexTupleTorEquiv (F : Type*) [Field F] (facets : Finset (Finset α))
    {a b c d e f : α} (hab : a ≠ b) (hbc : b ≠ c) (hcd : c ≠ d) (hde : d ≠ e) (hef : e ≠ f)
    (hfa : f ≠ a) (hac : a ≠ c) (hbd : b ≠ d) (hce : c ≠ e) (hdf : d ≠ f)
    (ha : IsFaceOf (↑facets : Set (Finset α)) {a}) (hb : IsFaceOf (↑facets : Set (Finset α)) {b})
    (hc : IsFaceOf (↑facets : Set (Finset α)) {c}) (hd : IsFaceOf (↑facets : Set (Finset α)) {d})
    (he : IsFaceOf (↑facets : Set (Finset α)) {e}) (hf : IsFaceOf (↑facets : Set (Finset α)) {f})
    (hab_f : IsFaceOf (↑facets : Set (Finset α)) {a, b})
    (hbc_f : IsFaceOf (↑facets : Set (Finset α)) {b, c})
    (hcd_f : IsFaceOf (↑facets : Set (Finset α)) {c, d})
    (hde_f : IsFaceOf (↑facets : Set (Finset α)) {d, e})
    (hef_f : IsFaceOf (↑facets : Set (Finset α)) {e, f})
    (hfa_f : IsFaceOf (↑facets : Set (Finset α)) {f, a})
    (hdf_nf : ¬ IsFaceOf (↑facets : Set (Finset α)) {d, f}) :
    F ≃ₗ[F] ↥(F ∙ srHexTupleTorClass F facets a b c d e f) :=
  LinearEquiv.toSpanNonzeroSingleton F _ (srHexTupleTorClass F facets a b c d e f)
    (srHexTupleTorClass_ne_zero F facets hab hbc hcd hde hef hfa hac hbd hce hdf ha hb hc hd he hf
      hab_f hbc_f hcd_f hde_f hef_f hfa_f hdf_nf)

end GaloisForLFunctions.HTGeometry
