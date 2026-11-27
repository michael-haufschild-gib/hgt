import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.WeilDeligneOperations

/-! A semisimple unramified Weil–Deligne representation is determined by
the multiset of its arithmetic Frobenius eigenvalues. -/

noncomputable section

open NumberField IsDedekindDomain Module Polynomial
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.WeilDeligne

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

namespace Unram

variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

private theorem exists_eigenbasis {f : End ℂ V} (hf : f.IsSemisimple) :
    ∃ (b : Basis (Fin (finrank ℂ V)) ℂ V) (c : Fin (finrank ℂ V) → ℂ), ∀ i, f (b i) = c i • b i := by
  obtain ⟨s, hs, hspan, hli⟩ := exists_linearIndependent ℂ (⋃ α, (f.eigenspace α : Set V))
  have htop : ⊤ ≤ Submodule.span ℂ (Set.range ((↑) : s → V)) := by
    rw [Subtype.range_coe, hspan, Submodule.span_iUnion, ← hf.iSup_eigenspace_eq_top]
    simp
  let b0 : Basis s ℂ V := Basis.mk hli htop
  let b := b0.reindex (b0.indexEquiv (finBasis ℂ V))
  have hb : ∀ i, ∃ α : ℂ, f (b i) = α • b i := by
    intro i
    have : b i ∈ s := by
      simp only [b, b0, Basis.reindex_apply, Basis.mk_apply]
      exact Subtype.prop _
    obtain ⟨α, hα⟩ := Set.mem_iUnion.mp (hs this)
    exact ⟨α, End.mem_eigenspace_iff.mp hα⟩
  choose c hc using hb
  exact ⟨b, c, hc⟩

private theorem apply_of_eigen {a : WDRep h V} (ha : a.Unr) {v : V} {c : ℂˣ}
    (hv : a.ρ (frob h) v = (c : ℂ) • v) (σ : Weil h) : a.ρ σ v = (c : ℂ) ^ deg σ • v := by
  have hc : (c : ℂ) ≠ 0 := c.ne_zero
  have hinv : a.ρ (frob h)⁻¹ v = (c : ℂ)⁻¹ • v := by
    have := congrArg (a.ρ (frob h)⁻¹) hv
    rw [← End.mul_apply, ← map_mul, inv_mul_cancel, map_one, End.one_apply, map_smul] at this
    rw [eq_inv_smul_iff₀ hc, ← this]
  have hk : ∀ k : ℤ, a.ρ (frob h ^ k) v = (c : ℂ) ^ k • v := by
    intro k
    induction k using Int.induction_on with
    | zero => simp
    | succ k ih =>
      rw [zpow_add_one, map_mul, End.mul_apply, hv, map_smul, ih, smul_smul, zpow_add_one₀ hc,
        mul_comm]
    | pred k ih =>
      rw [zpow_sub_one, map_mul, End.mul_apply, hinv, map_smul, ih, smul_smul, zpow_sub_one₀ hc,
        mul_comm]
  obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul (deg_frob (h := h)) σ
  conv_lhs => rw [hτ]
  rw [map_mul, ha.2, mul_one, hk]

private theorem mk_eq_diag {ι : Type} [Fintype ι] {a : WDRep h V} (ha : a.Unr) (b : Basis ι ℂ V)
    (c : ι → ℂˣ) (hb : ∀ i, a.ρ (frob h) (b i) = (c i : ℂ) • b i) :
    WD.mk a = WD.mk (WDRep.diag (h := h) c) := by
  classical
  refine WD.sound ⟨b.equivFun, fun σ v => ?_, fun v => by simp [ha.1]⟩
  have : b.equivFun.toLinearMap ∘ₗ a.ρ σ = (WDRep.diag (h := h) c).ρ σ ∘ₗ b.equivFun.toLinearMap := by
    refine b.ext fun i => funext fun j => ?_
    by_cases hij : i = j
    · subst hij; simp [apply_of_eigen ha (hb i)]
    · simp [apply_of_eigen ha (hb i), hij]
  exact LinearMap.congr_fun this v

theorem exists_diag {x : WD h} (hx : x.unr) :
    ∃ (n : ℕ) (c : Fin n → ℂˣ), x = WD.mk (WDRep.diag (h := h) c) := by
  obtain ⟨n, a, rfl⟩ := WD.exists_rep x
  obtain ⟨b, c, hc⟩ := exists_eigenbasis (a.semisimple (frob h))
  have h0 : ∀ i, c i ≠ 0 := by
    intro i hi
    have := congrArg (a.ρ (frob h)⁻¹) (hc i)
    rw [← End.mul_apply, ← map_mul, inv_mul_cancel, map_one, End.one_apply, hi, zero_smul,
      map_zero] at this
    exact b.ne_zero i this
  exact ⟨_, fun i => Units.mk0 (c i) (h0 i), mk_eq_diag ((WD.unr_mk a).mp hx) b _ hc⟩

private theorem exists_equiv_of_map_eq {ι κ α : Type} [Fintype ι] [Fintype κ] {c : ι → α} {d : κ → α}
    (hcd : Finset.univ.val.map c = Finset.univ.val.map d) : ∃ e : ι ≃ κ, ∀ i, d (e i) = c i := by
  classical
  have : ∀ z, Nonempty ({i // c i = z} ≃ {k // d k = z}) := by
    intro z
    rw [← Fintype.card_eq, Fintype.card_subtype, Fintype.card_subtype]
    have := congrArg (Multiset.count z) hcd
    rw [Multiset.count_map, Multiset.count_map] at this
    simp only [Finset.card, Finset.filter_val]
    simpa only [eq_comm] using this
  exact ⟨Equiv.ofFiberEquiv fun z => (this z).some, Equiv.ofFiberEquiv_map _⟩

private theorem diag_eq_diag {ι κ : Type} [Fintype ι] [Fintype κ] {c : ι → ℂˣ} {d : κ → ℂˣ}
    (hcd : (Finset.univ.val.map fun i => (c i : ℂ)) = Finset.univ.val.map fun k => (d k : ℂ)) :
    WD.mk (WDRep.diag (h := h) c) = WD.mk (WDRep.diag (h := h) d) := by
  obtain ⟨e, he⟩ := exists_equiv_of_map_eq hcd.symm
  refine WD.sound ⟨LinearEquiv.funCongrLeft ℂ ℂ e, fun σ v => funext fun k => ?_, fun v => by simp⟩
  simp [he]

end Unram

namespace WD

/-- The full multiset of eigenvalues of arithmetic Frobenius. -/
def frobEig (x : WD h) : Multiset ℂ := (x.charpoly (frob h)).roots

theorem frobEig_lpUnr {ι : Type} [Fintype ι] (c : ι → ℂˣ) :
    (lpUnr (h := h) c).frobEig = Finset.univ.val.map fun i => (c i : ℂ) := by
  rw [frobEig, charpoly_lpUnr_frob]
  change ((Finset.univ.val.map fun i => X - C (c i : ℂ)).prod).roots = _
  rw [show (Finset.univ.val.map fun i => X - C (c i : ℂ)) =
      (Finset.univ.val.map fun i => (c i : ℂ)).map (fun z => X - C z) from by
    rw [Multiset.map_map]
    rfl]
  exact roots_multiset_prod_X_sub_C _

/-- Equal Frobenius multisets identify unramified classes. -/
theorem eq_of_unr_of_frobEig {x y : WD h} (hx : x.unr) (hy : y.unr)
    (he : x.frobEig = y.frobEig) : x = y := by
  obtain ⟨n, c, rfl⟩ := Unram.exists_diag hx
  obtain ⟨m, d, rfl⟩ := Unram.exists_diag hy
  change (lpUnr (h := h) c).frobEig = (lpUnr (h := h) d).frobEig at he
  rw [frobEig_lpUnr, frobEig_lpUnr] at he
  exact Unram.diag_eq_diag he

/-- Vanishing monodromy and unipotent inertia characterize the unramified
classes because the Weil action is semisimple. -/
theorem unr_iff_inertia (x : WD h) :
    x.unr ↔ x.mono0 ∧ ∀ σ : Ine (F := E) A, x.charpoly (ineIncl h σ) = (X - 1) ^ x.lpDim := by
  obtain ⟨n, a, rfl⟩ := exists_rep x
  rw [unr_mk, mono0_mk, lpDim_mk, WDRep.Unr]
  refine and_congr Iff.rfl ?_
  constructor
  · intro ha σ
    rw [charpoly_mk, ha, LinearMap.charpoly_one]
  · intro ha σ
    have hc := ha σ
    rw [charpoly_mk] at hc
    have hn := LinearMap.aeval_self_charpoly (a.ρ (ineIncl h σ))
    rw [hc, map_pow, map_sub, aeval_X, map_one] at hn
    have hs : End.IsSemisimple (a.ρ (ineIncl h σ) - 1) := by
      simpa only [map_one] using
        (End.isSemisimple_sub_algebraMap_iff (μ := (1 : ℂ))).mpr (a.semisimple (ineIncl h σ))
    exact sub_eq_zero.mp (End.eq_zero_of_isNilpotent_isSemisimple ⟨_, hn⟩ hs)

end WD
end GlobalTheory.WeilDeligne
