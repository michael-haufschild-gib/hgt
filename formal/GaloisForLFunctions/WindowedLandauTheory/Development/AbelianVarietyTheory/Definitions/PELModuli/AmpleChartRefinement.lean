import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.LineBundlePowerExtension

/-! Coordinate ratios generate the ring on the nonzero locus of an additional section. -/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace GlobalTheory.AmpleLocal

variable {Z : Scheme.{0}}

variable {ι : Type} {U : ι → Z.Opens} {G : ι → Fn Z}
  (hU : ∀ z, ∃ i, z ∈ U i) (hG : ∀ i z, IsUnit (G i z))
include hU hG

/-- Enlarge the family of generators by considering the nonvanishing locus of another section. -/
theorem extra_section {T : Type} [Finite T] {W₀ : Z.Opens} {N d : ℕ} {s : T → Fn Z} (hs : ∀ j, Sc U G W₀ N (s j))
    {D : T → Z.Opens} (hD : ∀ j, IsLoc (D j) W₀ (s j)) (cov : ∀ z ∈ W₀, ∃ j, z ∈ D j) (aff : ∀ j, IsAffineOpen (D j))
    {S₀ : Set (Fn Z)} (hS₀ : ∀ x ∈ S₀, x ∈ Reg W₀) (gen : ∀ j, Gen (D j) (S₀ ∪ Set.range fun m => s m * inv (s j)))
    {τ : Fn Z} (hτ : Sc U G W₀ (N * (d + 1)) τ) {W : Z.Opens} (hW : IsLoc W W₀ τ) :
    IsAffineOpen W ∧ Gen W (S₀ ∪ Set.range fun p : T × T => s p.2 * s p.1 ^ d * inv τ) := by
  set u₀ : T × T → Fn Z := fun p => s p.2 * s p.1 ^ d * inv τ with hu₀
  let B := Subring.closure (S₀ ∪ Set.range u₀)
  let u : T × T → B := fun p => ⟨u₀ p, Subring.subset_closure (Or.inr ⟨p, rfl⟩)⟩
  have hB : B ≤ Reg W := Subring.closure_le.2 (by
    rintro x (hx | ⟨p, rfl⟩)
    · exact reg_mono hW.le (hS₀ x hx)
    · refine Sc.ratio hU hG ?_ hτ hW
      rw [mul_add, mul_one, add_comm]
      exact (hs _).mul ((hs _).pow d))
  let v : T → Fn Z := fun j => τ * inv (s j ^ (d + 1))
  have hv : ∀ j, v j ∈ Reg (D j) := fun j => Sc.ratio hU hG hτ ((hs j).pow _) fun z =>
    (hD j z).trans (and_congr_right' (isUnit_pow_iff d.succ_ne_zero).symm)
  have vu : ∀ j, ∀ z ∈ D j ⊓ W, v j z * u₀ (j, j) z = 1 := fun j z hz => by
    have h₁ := Ring.mul_inverse_cancel _ (((hD j).unit hz.1).pow (d + 1))
    have h₂ := Ring.mul_inverse_cancel _ (hW.unit hz.2)
    show τ z * Ring.inverse (s j z ^ (d + 1)) * (s j z * s j z ^ d * Ring.inverse (τ z)) = 1
    linear_combination (τ z * Ring.inverse (τ z)) * h₁ + h₂
  have l₁ : ∀ j, IsLoc (D j ⊓ W) (D j) (v j) := fun j z =>
    ⟨fun hz => ⟨hz.1, IsUnit.of_mul_eq_one _ (vu j z hz)⟩, fun hz =>
      ⟨hz.1, (hW z).2 ⟨(hD j).le hz.1, isUnit_of_mul_isUnit_left hz.2⟩⟩⟩
  have l₂ : ∀ j, IsLoc (D j ⊓ W) W (u₀ (j, j)) := fun j z =>
    ⟨fun hz => ⟨hz.2, IsUnit.of_mul_eq_one_right _ (vu j z hz)⟩, fun hz =>
      ⟨(hD j z).2 ⟨hW.le hz.1, isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hz.2)⟩, hz.1⟩⟩
  have aff' : ∀ j, IsAffineOpen (D j ⊓ W) := fun j => (l₁ j).affine (hv j) (aff j)
  have rat : ∀ j m, ∀ z ∈ D j ⊓ W, u₀ (j, j) z * (s m z * Ring.inverse (s j z)) = u₀ (j, m) z := fun j m z hz => by
    have h₁ := Ring.mul_inverse_cancel _ ((hD j).unit hz.1)
    show s j z * s j z ^ d * Ring.inverse (τ z) * _ = s m z * s j z ^ d * Ring.inverse (τ z)
    linear_combination (s m z * s j z ^ d * Ring.inverse (τ z)) * h₁
  have cpt : IsCompact (W : Set Z) := by
    have : (W : Set Z) = ⋃ j, ((D j ⊓ W : Z.Opens) : Set Z) := Set.ext fun z =>
      ⟨fun hz => (cov z (hW.le hz)).elim fun j hj => Set.mem_iUnion.2 ⟨j, hj, hz⟩,
        fun hz => (Set.mem_iUnion.1 hz).elim fun j hj => hj.2⟩
    rw [this]
    exact isCompact_iUnion fun j => (aff' j).isCompact
  set I := Ideal.span (Set.range u) with hI
  have uI : ∀ p, u p ∈ I := fun p => Ideal.subset_span (Set.mem_range_self p)
  have deep : ∀ j, ∃ e : ℕ, u (j, j) ^ e ∈ van B W ⊔ I ^ (e + 1) := fun j => by
    obtain ⟨b, hb, eb⟩ := gen j _ (hv j)
    obtain ⟨e, x, hx, ex⟩ : ∃ e : ℕ, ∃ x ∈ I ^ e, ∀ z ∈ D j ⊓ W, u₀ (j, j) z ^ e * b z = x.1 z := by
      clear eb
      induction hb using Subring.closure_induction with
      | mem x hx =>
        rcases hx with hx | ⟨m, rfl⟩
        · exact ⟨0, ⟨x, Subring.subset_closure (Or.inl hx)⟩, by simp, fun z _ => by rw [pow_zero, one_mul]⟩
        · exact ⟨1, u (j, m), by rw [pow_one]; exact uI _, fun z hz => by rw [pow_one]; exact rat j m z hz⟩
      | zero => exact ⟨0, 0, zero_mem _, fun _ _ => mul_zero _⟩
      | one => exact ⟨0, 1, by simp, fun _ _ => by rw [pow_zero, one_mul]; rfl⟩
      | add x y _ _ hx hy =>
        obtain ⟨n, a, ha, e⟩ := hx
        obtain ⟨m, b, hb, e'⟩ := hy
        refine ⟨n + m, a * u (j, j) ^ m + u (j, j) ^ n * b, ?_, fun z hz => ?_⟩
        · rw [pow_add]
          exact add_mem (Ideal.mul_mem_mul ha (Ideal.pow_mem_pow (uI _) _))
            (Ideal.mul_mem_mul (Ideal.pow_mem_pow (uI _) _) hb)
        · show u₀ (j, j) z ^ (n + m) * (x z + y z) = a.1 z * u₀ (j, j) z ^ m + u₀ (j, j) z ^ n * b.1 z
          rw [← e z hz, ← e' z hz]; ring
      | neg x _ hx =>
        obtain ⟨n, a, ha, e⟩ := hx
        refine ⟨n, -a, neg_mem ha, fun z hz => ?_⟩
        show u₀ (j, j) z ^ n * (-x z) = -a.1 z
        rw [← e z hz]; ring
      | mul x y _ _ hx hy =>
        obtain ⟨n, a, ha, e⟩ := hx
        obtain ⟨m, b, hb, e'⟩ := hy
        refine ⟨n + m, a * b, by rw [pow_add]; exact Ideal.mul_mem_mul ha hb, fun z hz => ?_⟩
        show u₀ (j, j) z ^ (n + m) * (x z * y z) = a.1 z * b.1 z
        rw [← e z hz, ← e' z hz]; ring
    obtain ⟨m, hm⟩ := kill cpt (l₂ j) (hB (u (j, j)).2) (hB (u (j, j) ^ e - u (j, j) * x).2) (fun z hz => by
      show u₀ (j, j) z ^ e - u₀ (j, j) z * x.1 z = 0
      rw [← ex z hz, ← eb z hz.1]
      linear_combination (-u₀ (j, j) z ^ e) * vu j z hz)
    refine ⟨m + e, Submodule.mem_sup.2 ⟨u (j, j) ^ m * (u (j, j) ^ e - u (j, j) * x), hm,
      u (j, j) ^ (m + 1) * x, ?_, by ring⟩⟩
    rw [show m + e + 1 = (m + 1) + e by ring, pow_add]
    exact Ideal.mul_mem_mul (Ideal.pow_mem_pow (uI _) _) hx
  have upow : ∀ i j, u (i, j) ^ (d + 1) = u (j, j) * u (i, i) ^ d := fun i j => Subtype.ext (by
    show u₀ (i, j) ^ (d + 1) = u₀ (j, j) * u₀ (i, i) ^ d
    simp only [hu₀]; ring)
  obtain ⟨c, hc, q, hq⟩ := exists_one_add_kill u (van B W) (fun ⟨i, j⟩ => by
    obtain ⟨e, he⟩ := deep j
    refine ⟨(d + 1) * e, ?_⟩
    rw [pow_mul, upow, mul_pow, ← pow_mul]
    have := Ideal.mul_mem_mul he (Ideal.pow_mem_pow (uI (i, i)) (d * e))
    rw [Ideal.sup_mul] at this
    have hle : van B W * I ^ (d * e) ⊔ I ^ (e + 1) * I ^ (d * e) ≤ van B W ⊔ I ^ ((d + 1) * e + 1) :=
      sup_le_sup Ideal.mul_le_right (le_of_eq (by ring))
    exact hle this)
  have hc0 : c ∈ van B W := fun z hz => by
    obtain ⟨j, hj⟩ := cov z (hW.le hz)
    exact (((l₂ j).unit ⟨hj, hz⟩).pow q).mul_left_eq_zero.1 (hq (j, j) z hz)
  have top : van B W ⊔ Ideal.span (Set.range fun j => u (j, j)) = ⊤ := by
    rw [← Ideal.radical_eq_top, Ideal.eq_top_iff_one]
    have hle : I ≤ (van B W ⊔ Ideal.span (Set.range fun j => u (j, j))).radical := by
      rw [hI, Ideal.span_le]
      rintro _ ⟨⟨i, j⟩, rfl⟩
      exact ⟨d + 1, by
        rw [upow]
        exact Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨j, rfl⟩))⟩
    have := sub_mem (Ideal.le_radical (Ideal.mem_sup_left hc0)) (hle hc)
    rwa [sub_sub_cancel] at this
  obtain ⟨h₁, h₂⟩ := local_global B hB (fun j => u (j, j)) top (fun j => D j ⊓ W) l₂ aff' fun j => by
    refine (Gen.loc (aff j) (l₁ j) (hv j) (gen j)).mono ?_
    rintro x (rfl | hx | ⟨m, rfl⟩)
    · refine ⟨u₀ (j, j), Subring.subset_closure (Or.inr (u (j, j)).2), fun z hz => ?_⟩
      exact ((Ring.eq_mul_inverse_iff_mul_eq _ _ _ ((l₁ j).unit hz)).2
        ((mul_comm _ _).trans (vu j z hz))).trans (one_mul _) |>.symm
    · exact ⟨x, Subring.subset_closure (Or.inr (Subring.subset_closure (Or.inl hx))), fun _ _ => rfl⟩
    · refine ⟨inv (u₀ (j, j)) * u₀ (j, m), mul_mem (Subring.subset_closure (Or.inl rfl))
        (Subring.subset_closure (Or.inr (u (j, m)).2)), fun z hz => ?_⟩
      show s m z * Ring.inverse (s j z) = Ring.inverse (u₀ (j, j) z) * u₀ (j, m) z
      rw [← rat j m z hz, ← mul_assoc, Ring.inverse_mul_cancel _ ((l₂ j).unit hz), one_mul]
  exact ⟨h₁, h₂.mono fun x hx => ⟨x, hx, fun _ _ => rfl⟩⟩

end GlobalTheory.AmpleLocal
