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

/-! ## C₄ Tor₂ as a concrete module class

The square (`C₄`) `Tor₂` class in the *concrete* Stanley–Reisner Koszul complex, in the same quotient
form as `C₅`/`C₆` — unifying the whole cycle family in one framework (the general `koszulTor` `C₄` class
`srC4KoszulTorClass` lives in a different, `Fin`-indexed, module). -/

omit [DecidableEq α] [Fintype α] in
/-- Sum of alternating `3`-tensors stays alternating. -/
theorem IsAlternating3_add {M : Type*} [AddCommGroup M] {b b' : α → α → α → M}
    (hb : IsAlternating3 b) (hb' : IsAlternating3 b') :
    IsAlternating3 (fun i j k => b i j k + b' i j k) where
  antisym12 i j k := by rw [hb.antisym12 i j k, hb'.antisym12 i j k, neg_add]
  antisym23 i j k := by rw [hb.antisym23 i j k, hb'.antisym23 i j k, neg_add]
  alt i j k h := by rw [hb.alt i j k h, hb'.alt i j k h, add_zero]

omit [DecidableEq α] [Fintype α] in
/-- The zero `3`-tensor is alternating. -/
theorem IsAlternating3_zero {M : Type*} [AddCommGroup M] :
    IsAlternating3 (0 : α → α → α → M) where
  antisym12 i j k := by simp
  antisym23 i j k := by simp
  alt i j k h := by simp

omit [DecidableEq α] [Fintype α] in
/-- Scaling an alternating `3`-tensor stays alternating. -/
theorem IsAlternating3_smul {M : Type*} [AddCommGroup M] [Module R M] {b : α → α → α → M}
    (hb : IsAlternating3 b) (r : R) : IsAlternating3 (fun i j k => r • b i j k) where
  antisym12 i j k := by rw [hb.antisym12 i j k, smul_neg]
  antisym23 i j k := by rw [hb.antisym23 i j k, smul_neg]
  alt i j k h := by rw [hb.alt i j k h, smul_zero]

/-- The submodule of alternating `3`-tensors over the Stanley–Reisner ring. -/
def alternating3Submodule (R : Type*) [CommRing R] (facets : Finset (Finset α)) :
    Submodule R (α → α → α → stanleyReisnerRing R facets) where
  carrier := {b | IsAlternating3 b}
  add_mem' hb hb' := IsAlternating3_add hb hb'
  zero_mem' := IsAlternating3_zero
  smul_mem' r _ hb := IsAlternating3_smul hb r

/-- The third Koszul differential as an `R`-linear map. -/
noncomputable def srKoszulBoundary3ₗ (R : Type*) [CommRing R] (facets : Finset (Finset α)) :
    (α → α → α → stanleyReisnerRing R facets) →ₗ[R]
      (α → α → stanleyReisnerRing R facets) where
  toFun b := srKoszulBoundary3 facets b
  map_add' b b' := by
    funext i j
    simp only [srKoszulBoundary3, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  map_smul' r b := by
    funext i j
    simp only [srKoszulBoundary3, Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
    exact Finset.sum_congr rfl (fun k _ => by rw [smul_mul_assoc])

/-- The degree-2 Koszul boundaries: `d₃` of alternating `3`-tensors. -/
noncomputable def srSquareEdgeBoundaries (R : Type*) [CommRing R] (facets : Finset (Finset α)) :
    Submodule R (α → α → stanleyReisnerRing R facets) :=
  Submodule.map (srKoszulBoundary3ₗ R facets) (alternating3Submodule R facets)

/-- The `C₄` second Koszul homology class in `(α → α → S) ⧸ (d₃-boundaries)`. -/
noncomputable def srSquareEdgeTorClass (R : Type*) [CommRing R] (facets : Finset (Finset α))
    (a b c d : α) :
    (α → α → stanleyReisnerRing R facets) ⧸ srSquareEdgeBoundaries R facets :=
  Submodule.Quotient.mk (srSquareEdgeCycle R facets a b c d)

/-- The concrete `C₄` `Tor₂` class is nonzero — the square cycle is not a `d₃`-boundary. -/
theorem srSquareEdgeTorClass_ne_zero (F : Type*) [Field F] (facets : Finset (Finset α))
    {a b c d : α} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (ha : IsFaceOf (↑facets : Set (Finset α)) {a}) (hb : IsFaceOf (↑facets : Set (Finset α)) {b})
    (hc : IsFaceOf (↑facets : Set (Finset α)) {c}) (hd : IsFaceOf (↑facets : Set (Finset α)) {d})
    (hab_f : IsFaceOf (↑facets : Set (Finset α)) {a, b})
    (hbc_f : IsFaceOf (↑facets : Set (Finset α)) {b, c})
    (hcd_f : IsFaceOf (↑facets : Set (Finset α)) {c, d})
    (had_f : IsFaceOf (↑facets : Set (Finset α)) {a, d})
    (hac_nf : ¬ IsFaceOf (↑facets : Set (Finset α)) {a, c})
    (hbd_nf : ¬ IsFaceOf (↑facets : Set (Finset α)) {b, d}) :
    srSquareEdgeTorClass F facets a b c d ≠ 0 := by
  intro h
  have hmem : srSquareEdgeCycle F facets a b c d ∈ srSquareEdgeBoundaries F facets :=
    (Submodule.Quotient.mk_eq_zero _).mp h
  obtain ⟨b3, hb3mem, hb3eq⟩ := Submodule.mem_map.mp hmem
  exact (srSquareEdge_secondKoszulHomology_nonzero facets hab hac had hbc hbd hcd
    ha hb hc hd hab_f hbc_f hcd_f had_f hac_nf hbd_nf).2 ⟨b3, hb3mem, hb3eq⟩

/-- **Concrete `C₄` `Tor₂` embedding.**  The square `Tor₂` class spans a free rank-one `F`-line. -/
noncomputable def srSquareEdgeTorEquiv (F : Type*) [Field F] (facets : Finset (Finset α))
    {a b c d : α} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (ha : IsFaceOf (↑facets : Set (Finset α)) {a}) (hb : IsFaceOf (↑facets : Set (Finset α)) {b})
    (hc : IsFaceOf (↑facets : Set (Finset α)) {c}) (hd : IsFaceOf (↑facets : Set (Finset α)) {d})
    (hab_f : IsFaceOf (↑facets : Set (Finset α)) {a, b})
    (hbc_f : IsFaceOf (↑facets : Set (Finset α)) {b, c})
    (hcd_f : IsFaceOf (↑facets : Set (Finset α)) {c, d})
    (had_f : IsFaceOf (↑facets : Set (Finset α)) {a, d})
    (hac_nf : ¬ IsFaceOf (↑facets : Set (Finset α)) {a, c})
    (hbd_nf : ¬ IsFaceOf (↑facets : Set (Finset α)) {b, d}) :
    F ≃ₗ[F] ↥(F ∙ srSquareEdgeTorClass F facets a b c d) :=
  LinearEquiv.toSpanNonzeroSingleton F _ (srSquareEdgeTorClass F facets a b c d)
    (srSquareEdgeTorClass_ne_zero F facets hab hac had hbc hbd hcd ha hb hc hd
      hab_f hbc_f hcd_f had_f hac_nf hbd_nf)

/-! ## C₄ Tor₂ retraction: `R` is an explicit direct summand

The alternating edge detector `+{cd}∘c_{ab} − {ad}∘c_{bc} + {ab}∘c_{cd} − {bc}∘c_{da}` is `R`-linear,
evaluates the square cycle to `1`, and annihilates every `d₃`-boundary of an alternating `3`-tensor.
Descended through the `d₃`-boundary quotient it is a retraction `Tor₂ → R` splitting the class
embedding — the explicit direct summand, matching the degree-1 `srHollowDetectorTor` retraction. -/

/-- Evaluation of a `2`-tensor at a fixed index pair, as an `R`-linear map. -/
def srEval2ₗ (R : Type*) [CommRing R] (facets : Finset (Finset α)) (i j : α) :
    (α → α → stanleyReisnerRing R facets) →ₗ[R] stanleyReisnerRing R facets where
  toFun t := t i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [DecidableEq α] [Fintype α] in
@[simp] theorem srEval2ₗ_apply (R : Type*) [CommRing R] (facets : Finset (Finset α)) (i j : α)
    (t : α → α → stanleyReisnerRing R facets) : srEval2ₗ R facets i j t = t i j := rfl

/-- The alternating edge detector of the square `C₄` `Tor₂` class, as an `R`-linear map. -/
noncomputable def srSquareEdgeDetectorₗ (R : Type*) [CommRing R] (facets : Finset (Finset α))
    (a b c d : α) (hab : a ≠ b) (hab_f : IsFaceOf (↑facets : Set (Finset α)) {a, b})
    (hbc : b ≠ c) (hbc_f : IsFaceOf (↑facets : Set (Finset α)) {b, c})
    (hcd : c ≠ d) (hcd_f : IsFaceOf (↑facets : Set (Finset α)) {c, d})
    (had : a ≠ d) (had_f : IsFaceOf (↑facets : Set (Finset α)) {a, d}) :
    (α → α → stanleyReisnerRing R facets) →ₗ[R] R :=
  (srPairDetector R facets c d hcd hcd_f).comp (srEval2ₗ R facets a b)
    - (srPairDetector R facets a d had had_f).comp (srEval2ₗ R facets b c)
    + (srPairDetector R facets a b hab hab_f).comp (srEval2ₗ R facets c d)
    - (srPairDetector R facets b c hbc hbc_f).comp (srEval2ₗ R facets d a)

omit [Fintype α] in
/-- The edge detector evaluates the square cycle to `1`. -/
theorem srSquareEdgeDetectorₗ_srSquareEdgeCycle (R : Type*) [CommRing R] (facets : Finset (Finset α))
    {a b c d : α} (hab : a ≠ b) (hab_f : IsFaceOf (↑facets : Set (Finset α)) {a, b})
    (hbc : b ≠ c) (hbc_f : IsFaceOf (↑facets : Set (Finset α)) {b, c})
    (hcd : c ≠ d) (hcd_f : IsFaceOf (↑facets : Set (Finset α)) {c, d})
    (had : a ≠ d) (had_f : IsFaceOf (↑facets : Set (Finset α)) {a, d}) (hac : a ≠ c) :
    srSquareEdgeDetectorₗ R facets a b c d hab hab_f hbc hbc_f hcd hcd_f had had_f
        (srSquareEdgeCycle R facets a b c d) = 1 := by
  simp only [srSquareEdgeDetectorₗ, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
    srEval2ₗ_apply]
  have t1 : srSquareEdgeCycle R facets a b c d a b
      = srVertexX R facets c * srVertexX R facets d := if_pos ⟨rfl, rfl⟩
  have t2 : srSquareEdgeCycle R facets a b c d b c = 0 := if_neg (fun h => hab h.1.symm)
  have t3 : srSquareEdgeCycle R facets a b c d c d = 0 := if_neg (fun h => hac h.1.symm)
  have t4 : srSquareEdgeCycle R facets a b c d d a = 0 := if_neg (fun h => had h.1.symm)
  rw [t1, t2, t3, t4, map_zero, map_zero, map_zero,
    srPairDetector_srVertexX_mul facets hcd hcd_f]
  ring

/-- The edge detector annihilates every `d₃`-boundary of an alternating `3`-tensor. -/
theorem srSquareEdgeDetectorₗ_srKoszulBoundary3 (R : Type*) [CommRing R]
    (facets : Finset (Finset α)) {a b c d : α}
    (hab : a ≠ b) (hab_f : IsFaceOf (↑facets : Set (Finset α)) {a, b})
    (hbc : b ≠ c) (hbc_f : IsFaceOf (↑facets : Set (Finset α)) {b, c})
    (hcd : c ≠ d) (hcd_f : IsFaceOf (↑facets : Set (Finset α)) {c, d})
    (had : a ≠ d) (had_f : IsFaceOf (↑facets : Set (Finset α)) {a, d})
    (ha : IsFaceOf (↑facets : Set (Finset α)) {a}) (hb : IsFaceOf (↑facets : Set (Finset α)) {b})
    (hc : IsFaceOf (↑facets : Set (Finset α)) {c}) (hd : IsFaceOf (↑facets : Set (Finset α)) {d})
    (b3 : α → α → α → stanleyReisnerRing R facets) (hb3 : IsAlternating3 b3) :
    srSquareEdgeDetectorₗ R facets a b c d hab hab_f hbc hbc_f hcd hcd_f had had_f
        (srKoszulBoundary3 facets b3) = 0 := by
  simp only [srSquareEdgeDetectorₗ, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
    srEval2ₗ_apply]
  rw [srPairDetector_srKoszulBoundary3 facets hcd hcd_f hc hd b3 a b,
      srPairDetector_srKoszulBoundary3 facets had had_f ha hd b3 b c,
      srPairDetector_srKoszulBoundary3 facets hab hab_f ha hb b3 c d,
      srPairDetector_srKoszulBoundary3 facets hbc hbc_f hb hc b3 d a]
  have e1 : b3 b c a = b3 a b c := by rw [hb3.antisym23 b c a, hb3.antisym12 b a c, neg_neg]
  have e2 : b3 d a b = b3 a b d := by rw [hb3.antisym12 d a b, hb3.antisym23 a d b, neg_neg]
  have e3 : b3 c d b = b3 b c d := by rw [hb3.antisym23 c d b, hb3.antisym12 c b d, neg_neg]
  have e4 : b3 d a c = b3 c d a := by rw [hb3.antisym23 d a c, hb3.antisym12 d c a, neg_neg]
  rw [e1, e2, e3, e4]
  abel

/-- The descended edge detector `Tor₂ → R` on the `d₃`-boundary quotient. -/
noncomputable def srSquareEdgeDetectorTor (R : Type*) [CommRing R] (facets : Finset (Finset α))
    (a b c d : α) (hab : a ≠ b) (hab_f : IsFaceOf (↑facets : Set (Finset α)) {a, b})
    (hbc : b ≠ c) (hbc_f : IsFaceOf (↑facets : Set (Finset α)) {b, c})
    (hcd : c ≠ d) (hcd_f : IsFaceOf (↑facets : Set (Finset α)) {c, d})
    (had : a ≠ d) (had_f : IsFaceOf (↑facets : Set (Finset α)) {a, d})
    (ha : IsFaceOf (↑facets : Set (Finset α)) {a}) (hb : IsFaceOf (↑facets : Set (Finset α)) {b})
    (hc : IsFaceOf (↑facets : Set (Finset α)) {c}) (hd : IsFaceOf (↑facets : Set (Finset α)) {d}) :
    ((α → α → stanleyReisnerRing R facets) ⧸ srSquareEdgeBoundaries R facets) →ₗ[R] R :=
  Submodule.liftQ (srSquareEdgeBoundaries R facets)
    (srSquareEdgeDetectorₗ R facets a b c d hab hab_f hbc hbc_f hcd hcd_f had had_f)
    (by
      simp only [srSquareEdgeBoundaries, Submodule.map_le_iff_le_comap]
      intro b3 hb3
      simp only [Submodule.mem_comap, LinearMap.mem_ker]
      exact srSquareEdgeDetectorₗ_srKoszulBoundary3 R facets hab hab_f hbc hbc_f hcd hcd_f had had_f
        ha hb hc hd b3 hb3)

/-- **The descended edge detector is `1` on the square `Tor₂` class** — hence a retraction splitting the
class embedding, so `R` is an explicit direct summand of the concrete `C₄` second Koszul homology. -/
theorem srSquareEdgeDetectorTor_class (R : Type*) [CommRing R] (facets : Finset (Finset α))
    {a b c d : α} (hab : a ≠ b) (hab_f : IsFaceOf (↑facets : Set (Finset α)) {a, b})
    (hbc : b ≠ c) (hbc_f : IsFaceOf (↑facets : Set (Finset α)) {b, c})
    (hcd : c ≠ d) (hcd_f : IsFaceOf (↑facets : Set (Finset α)) {c, d})
    (had : a ≠ d) (had_f : IsFaceOf (↑facets : Set (Finset α)) {a, d})
    (ha : IsFaceOf (↑facets : Set (Finset α)) {a}) (hb : IsFaceOf (↑facets : Set (Finset α)) {b})
    (hc : IsFaceOf (↑facets : Set (Finset α)) {c}) (hd : IsFaceOf (↑facets : Set (Finset α)) {d})
    (hac : a ≠ c) :
    srSquareEdgeDetectorTor R facets a b c d hab hab_f hbc hbc_f hcd hcd_f had had_f ha hb hc hd
        (srSquareEdgeTorClass R facets a b c d) = 1 := by
  simp only [srSquareEdgeDetectorTor, srSquareEdgeTorClass, Submodule.liftQ_apply]
  exact srSquareEdgeDetectorₗ_srSquareEdgeCycle R facets hab hab_f hbc hbc_f hcd hcd_f had had_f hac

/-! ## C₅ Tor₃ retraction: `R` is an explicit direct summand -/

/-- Evaluation of a `3`-tensor at a fixed index triple, as an `R`-linear map. -/
def srEval3ₗ (R : Type*) [CommRing R] (facets : Finset (Finset α)) (i j k : α) :
    (α → α → α → stanleyReisnerRing R facets) →ₗ[R] stanleyReisnerRing R facets where
  toFun t := t i j k
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [DecidableEq α] [Fintype α] in
@[simp] theorem srEval3ₗ_apply (R : Type*) [CommRing R] (facets : Finset (Finset α)) (i j k : α)
    (t : α → α → α → stanleyReisnerRing R facets) : srEval3ₗ R facets i j k t = t i j k := rfl

/-- The alternating detector of the pentagon `C₅` `Tor₃` class, as an `R`-linear map. -/
noncomputable def srPentTripleDetectorₗ (R : Type*) [CommRing R] (facets : Finset (Finset α))
    (a b c d e : α) (hab : a ≠ b) (hab_f : IsFaceOf (↑facets : Set (Finset α)) {a, b})
    (hbc : b ≠ c) (hbc_f : IsFaceOf (↑facets : Set (Finset α)) {b, c})
    (hcd : c ≠ d) (hcd_f : IsFaceOf (↑facets : Set (Finset α)) {c, d})
    (hde : d ≠ e) (hde_f : IsFaceOf (↑facets : Set (Finset α)) {d, e})
    (hea : e ≠ a) (hea_f : IsFaceOf (↑facets : Set (Finset α)) {e, a}) :
    (α → α → α → stanleyReisnerRing R facets) →ₗ[R] R :=
  (srPairDetector R facets a b hab hab_f).comp (srEval3ₗ R facets c d e)
    + (srPairDetector R facets b c hbc hbc_f).comp (srEval3ₗ R facets a d e)
    + (srPairDetector R facets c d hcd hcd_f).comp (srEval3ₗ R facets a b e)
    + (srPairDetector R facets d e hde hde_f).comp (srEval3ₗ R facets a b c)
    + (srPairDetector R facets e a hea hea_f).comp (srEval3ₗ R facets b c d)

omit [Fintype α] in
/-- The pentagon detector evaluates the `C₅` cycle to `1`. -/
theorem srPentTripleDetectorₗ_srPentTripleCycle (R : Type*) [CommRing R] (facets : Finset (Finset α))
    {a b c d e : α} (hab : a ≠ b) (hab_f : IsFaceOf (↑facets : Set (Finset α)) {a, b})
    (hbc : b ≠ c) (hbc_f : IsFaceOf (↑facets : Set (Finset α)) {b, c})
    (hcd : c ≠ d) (hcd_f : IsFaceOf (↑facets : Set (Finset α)) {c, d})
    (hde : d ≠ e) (hde_f : IsFaceOf (↑facets : Set (Finset α)) {d, e})
    (hea : e ≠ a) (hea_f : IsFaceOf (↑facets : Set (Finset α)) {e, a})
    (hac : a ≠ c) (hbd : b ≠ d) (hce : c ≠ e) :
    srPentTripleDetectorₗ R facets a b c d e hab hab_f hbc hbc_f hcd hcd_f hde hde_f hea hea_f
        (srPentTripleCycle R facets a b c d e) = 1 := by
  have t0 : srPentTripleCycle R facets a b c d e c d e = 0 := if_neg (fun h => hac h.1.symm)
  have t1 : srPentTripleCycle R facets a b c d e a d e = 0 := if_neg (fun h => hbd h.2.1.symm)
  have t2 : srPentTripleCycle R facets a b c d e a b e = 0 := if_neg (fun h => hce h.2.2.symm)
  have t3 : srPentTripleCycle R facets a b c d e a b c
      = srVertexX R facets d * srVertexX R facets e := if_pos ⟨rfl, rfl, rfl⟩
  have t4 : srPentTripleCycle R facets a b c d e b c d = 0 := if_neg (fun h => hab h.1.symm)
  simp only [srPentTripleDetectorₗ, LinearMap.add_apply, LinearMap.comp_apply, srEval3ₗ_apply,
    t0, t1, t2, t3, t4, map_zero, add_zero, zero_add]
  rw [srPairDetector_srVertexX_mul facets hde hde_f]

/-- The pentagon detector annihilates every `d₄`-boundary of an alternating `4`-tensor. -/
theorem srPentTripleDetectorₗ_srKoszulBoundary4 (R : Type*) [CommRing R]
    (facets : Finset (Finset α)) {a b c d e : α}
    (hab : a ≠ b) (hab_f : IsFaceOf (↑facets : Set (Finset α)) {a, b})
    (hbc : b ≠ c) (hbc_f : IsFaceOf (↑facets : Set (Finset α)) {b, c})
    (hcd : c ≠ d) (hcd_f : IsFaceOf (↑facets : Set (Finset α)) {c, d})
    (hde : d ≠ e) (hde_f : IsFaceOf (↑facets : Set (Finset α)) {d, e})
    (hea : e ≠ a) (hea_f : IsFaceOf (↑facets : Set (Finset α)) {e, a})
    (ha : IsFaceOf (↑facets : Set (Finset α)) {a}) (hb : IsFaceOf (↑facets : Set (Finset α)) {b})
    (hc : IsFaceOf (↑facets : Set (Finset α)) {c}) (hd : IsFaceOf (↑facets : Set (Finset α)) {d})
    (he : IsFaceOf (↑facets : Set (Finset α)) {e})
    (b4 : α → α → α → α → stanleyReisnerRing R facets) (hb4 : IsAlternating4 b4) :
    srPentTripleDetectorₗ R facets a b c d e hab hab_f hbc hbc_f hcd hcd_f hde hde_f hea hea_f
        (srKoszulBoundary4 facets b4) = 0 := by
  simp only [srPentTripleDetectorₗ, LinearMap.add_apply, LinearMap.comp_apply, srEval3ₗ_apply]
  rw [srPairDetector_srKoszulBoundary4 facets hab hab_f ha hb b4 c d e,
      srPairDetector_srKoszulBoundary4 facets hbc hbc_f hb hc b4 a d e,
      srPairDetector_srKoszulBoundary4 facets hcd hcd_f hc hd b4 a b e,
      srPairDetector_srKoszulBoundary4 facets hde hde_f hd he b4 a b c,
      srPairDetector_srKoszulBoundary4 facets hea hea_f he ha b4 b c d]
  have r1 : b4 c d e b = -b4 b c d e := by
    rw [hb4.antisym34 c d e b, hb4.antisym23 c d b e, hb4.antisym12 c b d e]; ring
  have r2 : b4 a d e c = -b4 c d e a := by
    rw [hb4.antisym12 a d e c, hb4.antisym23 d a e c, hb4.antisym34 d e a c,
      hb4.antisym23 d e c a, hb4.antisym12 d c e a]; ring
  have r3 : b4 a b e d = -b4 a d e b := by
    rw [hb4.antisym23 a b e d, hb4.antisym34 a e b d, hb4.antisym23 a e d b]; ring
  have r4 : b4 a b c e = -b4 a b e c := by rw [hb4.antisym34 a b c e]
  have r5 : b4 b c d a = -b4 a b c d := by
    rw [hb4.antisym34 b c d a, hb4.antisym23 b c a d, hb4.antisym12 b a c d]; ring
  rw [r1, r2, r3, r4, r5]
  simp only [map_neg]
  abel

/-- The descended pentagon detector `Tor₃ → R` on the `d₄`-boundary quotient. -/
noncomputable def srPentTripleDetectorTor (R : Type*) [CommRing R] (facets : Finset (Finset α))
    (a b c d e : α) (hab : a ≠ b) (hab_f : IsFaceOf (↑facets : Set (Finset α)) {a, b})
    (hbc : b ≠ c) (hbc_f : IsFaceOf (↑facets : Set (Finset α)) {b, c})
    (hcd : c ≠ d) (hcd_f : IsFaceOf (↑facets : Set (Finset α)) {c, d})
    (hde : d ≠ e) (hde_f : IsFaceOf (↑facets : Set (Finset α)) {d, e})
    (hea : e ≠ a) (hea_f : IsFaceOf (↑facets : Set (Finset α)) {e, a})
    (ha : IsFaceOf (↑facets : Set (Finset α)) {a}) (hb : IsFaceOf (↑facets : Set (Finset α)) {b})
    (hc : IsFaceOf (↑facets : Set (Finset α)) {c}) (hd : IsFaceOf (↑facets : Set (Finset α)) {d})
    (he : IsFaceOf (↑facets : Set (Finset α)) {e}) :
    ((α → α → α → stanleyReisnerRing R facets) ⧸ srPentTripleBoundaries R facets) →ₗ[R] R :=
  Submodule.liftQ (srPentTripleBoundaries R facets)
    (srPentTripleDetectorₗ R facets a b c d e hab hab_f hbc hbc_f hcd hcd_f hde hde_f hea hea_f)
    (by
      simp only [srPentTripleBoundaries, Submodule.map_le_iff_le_comap]
      intro b4 hb4
      simp only [Submodule.mem_comap, LinearMap.mem_ker]
      exact srPentTripleDetectorₗ_srKoszulBoundary4 R facets hab hab_f hbc hbc_f hcd hcd_f hde hde_f
        hea hea_f ha hb hc hd he b4 hb4)

/-- **The descended pentagon detector is `1` on the `C₅` `Tor₃` class** — a retraction splitting the
class embedding, so `R` is an explicit direct summand of the third Koszul homology. -/
theorem srPentTripleDetectorTor_class (R : Type*) [CommRing R] (facets : Finset (Finset α))
    {a b c d e : α} (hab : a ≠ b) (hab_f : IsFaceOf (↑facets : Set (Finset α)) {a, b})
    (hbc : b ≠ c) (hbc_f : IsFaceOf (↑facets : Set (Finset α)) {b, c})
    (hcd : c ≠ d) (hcd_f : IsFaceOf (↑facets : Set (Finset α)) {c, d})
    (hde : d ≠ e) (hde_f : IsFaceOf (↑facets : Set (Finset α)) {d, e})
    (hea : e ≠ a) (hea_f : IsFaceOf (↑facets : Set (Finset α)) {e, a})
    (ha : IsFaceOf (↑facets : Set (Finset α)) {a}) (hb : IsFaceOf (↑facets : Set (Finset α)) {b})
    (hc : IsFaceOf (↑facets : Set (Finset α)) {c}) (hd : IsFaceOf (↑facets : Set (Finset α)) {d})
    (he : IsFaceOf (↑facets : Set (Finset α)) {e})
    (hac : a ≠ c) (hbd : b ≠ d) (hce : c ≠ e) :
    srPentTripleDetectorTor R facets a b c d e hab hab_f hbc hbc_f hcd hcd_f hde hde_f hea hea_f
        ha hb hc hd he (srPentTripleTorClass R facets a b c d e) = 1 := by
  simp only [srPentTripleDetectorTor, srPentTripleTorClass, Submodule.liftQ_apply]
  exact srPentTripleDetectorₗ_srPentTripleCycle R facets hab hab_f hbc hbc_f hcd hcd_f hde hde_f
    hea hea_f hac hbd hce

/-! ## C₆ Tor₄ retraction: `R` is an explicit direct summand -/

/-- Evaluation of a `4`-tensor at a fixed index quadruple, as an `R`-linear map. -/
def srEval4ₗ (R : Type*) [CommRing R] (facets : Finset (Finset α)) (i j k l : α) :
    (α → α → α → α → stanleyReisnerRing R facets) →ₗ[R] stanleyReisnerRing R facets where
  toFun t := t i j k l
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [DecidableEq α] [Fintype α] in
@[simp] theorem srEval4ₗ_apply (R : Type*) [CommRing R] (facets : Finset (Finset α)) (i j k l : α)
    (t : α → α → α → α → stanleyReisnerRing R facets) : srEval4ₗ R facets i j k l t = t i j k l := rfl

/-- The alternating detector of the hexagon `C₆` `Tor₄` class, as an `R`-linear map. -/
noncomputable def srHexTupleDetectorₗ (R : Type*) [CommRing R] (facets : Finset (Finset α))
    (a b c d e f : α) (hab : a ≠ b) (hab_f : IsFaceOf (↑facets : Set (Finset α)) {a, b})
    (hbc : b ≠ c) (hbc_f : IsFaceOf (↑facets : Set (Finset α)) {b, c})
    (hcd : c ≠ d) (hcd_f : IsFaceOf (↑facets : Set (Finset α)) {c, d})
    (hde : d ≠ e) (hde_f : IsFaceOf (↑facets : Set (Finset α)) {d, e})
    (hef : e ≠ f) (hef_f : IsFaceOf (↑facets : Set (Finset α)) {e, f})
    (hfa : f ≠ a) (hfa_f : IsFaceOf (↑facets : Set (Finset α)) {f, a}) :
    (α → α → α → α → stanleyReisnerRing R facets) →ₗ[R] R :=
  (srPairDetector R facets a b hab hab_f).comp (srEval4ₗ R facets c d e f)
    + (srPairDetector R facets b c hbc hbc_f).comp (srEval4ₗ R facets a d e f)
    + (srPairDetector R facets c d hcd hcd_f).comp (srEval4ₗ R facets a b e f)
    + (srPairDetector R facets d e hde hde_f).comp (srEval4ₗ R facets a b c f)
    + (srPairDetector R facets e f hef hef_f).comp (srEval4ₗ R facets a b c d)
    - (srPairDetector R facets f a hfa hfa_f).comp (srEval4ₗ R facets b c d e)

omit [Fintype α] in
/-- The hexagon detector evaluates the `C₆` cycle to `1`. -/
theorem srHexTupleDetectorₗ_srHexTupleCycle (R : Type*) [CommRing R] (facets : Finset (Finset α))
    {a b c d e f : α} (hab : a ≠ b) (hab_f : IsFaceOf (↑facets : Set (Finset α)) {a, b})
    (hbc : b ≠ c) (hbc_f : IsFaceOf (↑facets : Set (Finset α)) {b, c})
    (hcd : c ≠ d) (hcd_f : IsFaceOf (↑facets : Set (Finset α)) {c, d})
    (hde : d ≠ e) (hde_f : IsFaceOf (↑facets : Set (Finset α)) {d, e})
    (hef : e ≠ f) (hef_f : IsFaceOf (↑facets : Set (Finset α)) {e, f})
    (hfa : f ≠ a) (hfa_f : IsFaceOf (↑facets : Set (Finset α)) {f, a})
    (hac : a ≠ c) (hbd : b ≠ d) (hce : c ≠ e) (hdf : d ≠ f) :
    srHexTupleDetectorₗ R facets a b c d e f hab hab_f hbc hbc_f hcd hcd_f hde hde_f hef hef_f
        hfa hfa_f (srHexTupleCycle R facets a b c d e f) = 1 := by
  have t0 : srHexTupleCycle R facets a b c d e f c d e f = 0 := if_neg (fun h => hac h.1.symm)
  have t1 : srHexTupleCycle R facets a b c d e f a d e f = 0 := if_neg (fun h => hbd h.2.1.symm)
  have t2 : srHexTupleCycle R facets a b c d e f a b e f = 0 := if_neg (fun h => hce h.2.2.1.symm)
  have t3 : srHexTupleCycle R facets a b c d e f a b c f = 0 := if_neg (fun h => hdf h.2.2.2.symm)
  have t4 : srHexTupleCycle R facets a b c d e f a b c d
      = srVertexX R facets e * srVertexX R facets f := if_pos ⟨rfl, rfl, rfl, rfl⟩
  have t5 : srHexTupleCycle R facets a b c d e f b c d e = 0 := if_neg (fun h => hab h.1.symm)
  simp only [srHexTupleDetectorₗ, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    srEval4ₗ_apply, t0, t1, t2, t3, t4, t5, map_zero, add_zero, zero_add, sub_zero]
  rw [srPairDetector_srVertexX_mul facets hef hef_f]

/-- The hexagon detector annihilates every `d₅`-boundary of an alternating `5`-tensor. -/
theorem srHexTupleDetectorₗ_srKoszulBoundary5 (R : Type*) [CommRing R]
    (facets : Finset (Finset α)) {a b c d e f : α}
    (hab : a ≠ b) (hab_f : IsFaceOf (↑facets : Set (Finset α)) {a, b})
    (hbc : b ≠ c) (hbc_f : IsFaceOf (↑facets : Set (Finset α)) {b, c})
    (hcd : c ≠ d) (hcd_f : IsFaceOf (↑facets : Set (Finset α)) {c, d})
    (hde : d ≠ e) (hde_f : IsFaceOf (↑facets : Set (Finset α)) {d, e})
    (hef : e ≠ f) (hef_f : IsFaceOf (↑facets : Set (Finset α)) {e, f})
    (hfa : f ≠ a) (hfa_f : IsFaceOf (↑facets : Set (Finset α)) {f, a})
    (ha : IsFaceOf (↑facets : Set (Finset α)) {a}) (hb : IsFaceOf (↑facets : Set (Finset α)) {b})
    (hc : IsFaceOf (↑facets : Set (Finset α)) {c}) (hd : IsFaceOf (↑facets : Set (Finset α)) {d})
    (he : IsFaceOf (↑facets : Set (Finset α)) {e}) (hf : IsFaceOf (↑facets : Set (Finset α)) {f})
    (b5 : α → α → α → α → α → stanleyReisnerRing R facets) (hb5 : IsAlternating5 b5) :
    srHexTupleDetectorₗ R facets a b c d e f hab hab_f hbc hbc_f hcd hcd_f hde hde_f hef hef_f
        hfa hfa_f (srKoszulBoundary5 facets b5) = 0 := by
  simp only [srHexTupleDetectorₗ, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    srEval4ₗ_apply]
  rw [srPairDetector_srKoszulBoundary5 facets hab hab_f ha hb b5 c d e f,
      srPairDetector_srKoszulBoundary5 facets hbc hbc_f hb hc b5 a d e f,
      srPairDetector_srKoszulBoundary5 facets hcd hcd_f hc hd b5 a b e f,
      srPairDetector_srKoszulBoundary5 facets hde hde_f hd he b5 a b c f,
      srPairDetector_srKoszulBoundary5 facets hef hef_f he hf b5 a b c d,
      srPairDetector_srKoszulBoundary5 facets hfa hfa_f hf ha b5 b c d e]
  have ra : b5 c d e f b = b5 b c d e f := by
    rw [hb5.antisym45 c d e f b, hb5.antisym34 c d e b f, hb5.antisym23 c d b e f,
      hb5.antisym12 c b d e f]; ring
  have rb : b5 a d e f c = -b5 c d e f a := by
    rw [hb5.antisym45 a d e f c, hb5.antisym34 a d e c f, hb5.antisym23 a d c e f,
      hb5.antisym12 a c d e f, hb5.antisym23 c a d e f, hb5.antisym34 c d a e f,
      hb5.antisym45 c d e a f]; ring
  have rc : b5 a b e f d = -b5 a d e f b := by
    rw [hb5.antisym45 a b e f d, hb5.antisym34 a b e d f, hb5.antisym23 a b d e f,
      hb5.antisym34 a d b e f, hb5.antisym45 a d e b f]; ring
  have rd : b5 a b c f e = -b5 a b e f c := by
    rw [hb5.antisym45 a b c f e, hb5.antisym34 a b c e f, hb5.antisym45 a b e c f]; ring
  have re : b5 a b c d f = -b5 a b c f d := by rw [hb5.antisym45 a b c d f]
  have rf : b5 b c d e a = b5 a b c d e := by
    rw [hb5.antisym45 b c d e a, hb5.antisym34 b c d a e, hb5.antisym23 b c a d e,
      hb5.antisym12 b a c d e]; ring
  rw [ra, rb, rc, rd, re, rf]
  simp only [map_neg]
  abel

/-- The descended hexagon detector `Tor₄ → R` on the `d₅`-boundary quotient. -/
noncomputable def srHexTupleDetectorTor (R : Type*) [CommRing R] (facets : Finset (Finset α))
    (a b c d e f : α) (hab : a ≠ b) (hab_f : IsFaceOf (↑facets : Set (Finset α)) {a, b})
    (hbc : b ≠ c) (hbc_f : IsFaceOf (↑facets : Set (Finset α)) {b, c})
    (hcd : c ≠ d) (hcd_f : IsFaceOf (↑facets : Set (Finset α)) {c, d})
    (hde : d ≠ e) (hde_f : IsFaceOf (↑facets : Set (Finset α)) {d, e})
    (hef : e ≠ f) (hef_f : IsFaceOf (↑facets : Set (Finset α)) {e, f})
    (hfa : f ≠ a) (hfa_f : IsFaceOf (↑facets : Set (Finset α)) {f, a})
    (ha : IsFaceOf (↑facets : Set (Finset α)) {a}) (hb : IsFaceOf (↑facets : Set (Finset α)) {b})
    (hc : IsFaceOf (↑facets : Set (Finset α)) {c}) (hd : IsFaceOf (↑facets : Set (Finset α)) {d})
    (he : IsFaceOf (↑facets : Set (Finset α)) {e}) (hf : IsFaceOf (↑facets : Set (Finset α)) {f}) :
    ((α → α → α → α → stanleyReisnerRing R facets) ⧸ srHexTupleBoundaries R facets) →ₗ[R] R :=
  Submodule.liftQ (srHexTupleBoundaries R facets)
    (srHexTupleDetectorₗ R facets a b c d e f hab hab_f hbc hbc_f hcd hcd_f hde hde_f hef hef_f
      hfa hfa_f)
    (by
      simp only [srHexTupleBoundaries, Submodule.map_le_iff_le_comap]
      intro b5 hb5
      simp only [Submodule.mem_comap, LinearMap.mem_ker]
      exact srHexTupleDetectorₗ_srKoszulBoundary5 R facets hab hab_f hbc hbc_f hcd hcd_f hde hde_f
        hef hef_f hfa hfa_f ha hb hc hd he hf b5 hb5)

/-- **The descended hexagon detector is `1` on the `C₆` `Tor₄` class** — a retraction splitting the
class embedding, so `R` is an explicit direct summand of the fourth Koszul homology. -/
theorem srHexTupleDetectorTor_class (R : Type*) [CommRing R] (facets : Finset (Finset α))
    {a b c d e f : α} (hab : a ≠ b) (hab_f : IsFaceOf (↑facets : Set (Finset α)) {a, b})
    (hbc : b ≠ c) (hbc_f : IsFaceOf (↑facets : Set (Finset α)) {b, c})
    (hcd : c ≠ d) (hcd_f : IsFaceOf (↑facets : Set (Finset α)) {c, d})
    (hde : d ≠ e) (hde_f : IsFaceOf (↑facets : Set (Finset α)) {d, e})
    (hef : e ≠ f) (hef_f : IsFaceOf (↑facets : Set (Finset α)) {e, f})
    (hfa : f ≠ a) (hfa_f : IsFaceOf (↑facets : Set (Finset α)) {f, a})
    (ha : IsFaceOf (↑facets : Set (Finset α)) {a}) (hb : IsFaceOf (↑facets : Set (Finset α)) {b})
    (hc : IsFaceOf (↑facets : Set (Finset α)) {c}) (hd : IsFaceOf (↑facets : Set (Finset α)) {d})
    (he : IsFaceOf (↑facets : Set (Finset α)) {e}) (hf : IsFaceOf (↑facets : Set (Finset α)) {f})
    (hac : a ≠ c) (hbd : b ≠ d) (hce : c ≠ e) (hdf : d ≠ f) :
    srHexTupleDetectorTor R facets a b c d e f hab hab_f hbc hbc_f hcd hcd_f hde hde_f hef hef_f
        hfa hfa_f ha hb hc hd he hf (srHexTupleTorClass R facets a b c d e f) = 1 := by
  simp only [srHexTupleDetectorTor, srHexTupleTorClass, Submodule.liftQ_apply]
  exact srHexTupleDetectorₗ_srHexTupleCycle R facets hab hab_f hbc hbc_f hcd hcd_f hde hde_f hef hef_f
    hfa hfa_f hac hbd hce hdf

end GaloisForLFunctions.HTGeometry
