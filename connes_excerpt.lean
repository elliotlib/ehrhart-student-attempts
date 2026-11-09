-- ===== core definitions (lines 1-260) =====
import Mathlib

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

namespace ConnesRigidity

section

namespace FeedbackBooleanPolynomial

variable {ι : Type*} [DecidableEq ι]

@[simp]
theorem two_eq_zero_zmod_two : (2 : ZMod 2) = 0 := by
  rfl

theorem eq_one_of_ne_zero_zmod_two
    (a : ZMod 2) (ha : a ≠ 0) :
    a = 1 := by
  fin_cases a
  · exact (ha rfl).elim
  · rfl

abbrev StrictPair (ι : Type*) [LT ι] :=
  {p : ι × ι // p.1 < p.2}

structure BinaryQuadraticPolynomial
    (ι : Type*) [Fintype ι] [LinearOrder ι] where
  constant : ZMod 2
  linear : ι → ZMod 2
  quadratic : StrictPair ι → ZMod 2

end FeedbackBooleanPolynomial

end

section

universe u v

structure CountableDiscreteGroup where
  Carrier : Type u
  group : Group Carrier
  countable : Countable Carrier

namespace CountableDiscreteGroup

instance : CoeSort CountableDiscreteGroup (Type u) :=
  ⟨CountableDiscreteGroup.Carrier⟩

attribute [instance] group countable

end CountableDiscreteGroup

def conjugacyClass (G : CountableDiscreteGroup) (g : G) : Set G :=
  {h | ∃ x : G, h = x * g * x⁻¹}

def IsICC (G : CountableDiscreteGroup) : Prop :=
  Infinite G ∧ ∀ g : G, g ≠ 1 → Set.Infinite (conjugacyClass G g)

def GroupsIsomorphic (G H : CountableDiscreteGroup) : Prop :=
  Nonempty (G ≃* H)

abbrev UnitaryRepresentation
    (G : Type u) [Group G]
    (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :=
  G →* unitary (H →L[ℂ] H)

namespace UnitaryRepresentation

variable {G H : Type u} [Group G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def IsInvariant (π : UnitaryRepresentation G H) (ξ : H) : Prop :=
  ∀ g : G, (π g : H →L[ℂ] H) ξ = ξ

def HasAlmostInvariantUnitVectors (π : UnitaryRepresentation G H) : Prop :=
  ∀ (K : Finset G) (ε : ℝ), 0 < ε →
    ∃ ξ : H, ‖ξ‖ = 1 ∧ ∀ g ∈ K, ‖(π g : H →L[ℂ] H) ξ - ξ‖ < ε

end UnitaryRepresentation

def HasKazhdanPropertyT (G : CountableDiscreteGroup.{u}) : Prop :=
  ∀ (H : Type u)
    (_ : NormedAddCommGroup H)
    (_ : InnerProductSpace ℂ H)
    (_ : CompleteSpace H)
    (π : UnitaryRepresentation G H),
    π.HasAlmostInvariantUnitVectors →
      ∃ ξ : H, ξ ≠ 0 ∧ π.IsInvariant ξ

noncomputable section

open scoped NNReal ENNReal

abbrev GroupL2 (G : Type u) := lp (fun _ : G ↦ ℂ) 2

def l2Reindex {α : Type u} {β : Type v} (e : α ≃ β) :
    GroupL2 α ≃ₗᵢ[ℂ] GroupL2 β where
  toLinearEquiv :=
    { toFun := fun f ↦ ⟨(fun j : β ↦ f (e.symm j)), by
        change Memℓp (fun j : β ↦ f (e.symm j)) 2
        rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
        exact (e.symm.summable_iff).2
          ((lp.memℓp f).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal))⟩
      invFun := fun f ↦ ⟨(fun j : α ↦ f (e j)), by
        change Memℓp (fun j : α ↦ f (e j)) 2
        rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
        exact e.summable_iff.mpr
          ((lp.memℓp f).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal))⟩
      left_inv := by
        intro f
        ext i
        change f (e.symm (e i)) = f i
        simp
      right_inv := by
        intro f
        ext j
        change f (e (e.symm j)) = f j
        simp
      map_add' := by
        intro f g
        ext j
        rfl
      map_smul' := by
        intro c f
        ext j
        rfl }
  norm_map' := by
    intro f
    rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    congr 1
    exact e.symm.tsum_eq (fun i ↦ ‖f i‖ ^ (2 : ℝ≥0∞).toReal)

@[simp]
theorem l2Reindex_apply {α : Type u} {β : Type v} (e : α ≃ β)
    (f : GroupL2 α) (j : β) :
    l2Reindex e f j = f (e.symm j) :=
  rfl

@[simp]
theorem l2Reindex_symm {α : Type u} {β : Type v} (e : α ≃ β) :
    (l2Reindex e).symm = l2Reindex e.symm := by
  ext f i
  rfl

def leftRegularUnitary {G : Type u} [Group G] (g : G) :
    unitary (GroupL2 G →L[ℂ] GroupL2 G) :=
  Unitary.linearIsometryEquiv.symm (l2Reindex (Equiv.mulLeft g))

@[simp]
theorem leftRegularUnitary_apply {G : Type u} [Group G]
    (g : G) (f : GroupL2 G) (h : G) :
    (leftRegularUnitary g : GroupL2 G →L[ℂ] GroupL2 G) f h = f (g⁻¹ * h) := by
  rfl

def leftRegularRepresentation (G : Type u) [Group G] :
    G →* unitary (GroupL2 G →L[ℂ] GroupL2 G) where
  toFun := leftRegularUnitary
  map_one' := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro f
    ext h
    change f ((1 : G)⁻¹ * h) = f h
    simp
  map_mul' g h := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro f
    ext k
    change f ((g * h)⁻¹ * k) = f (h⁻¹ * (g⁻¹ * k))
    simp [mul_assoc]

def vonNeumannClosure
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : Set (H →L[ℂ] H)) :
    VonNeumannAlgebra H where
  toStarSubalgebra :=
    StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ S : Set (H →L[ℂ] H))
  centralizer_centralizer' := by
    change
      Set.centralizer
          (Set.centralizer
            ((StarSubalgebra.centralizer ℂ
              (StarSubalgebra.centralizer ℂ S : Set (H →L[ℂ] H))) :
                Set (H →L[ℂ] H))) =
        ((StarSubalgebra.centralizer ℂ
          (StarSubalgebra.centralizer ℂ S : Set (H →L[ℂ] H))) :
            Set (H →L[ℂ] H))
    rw [StarSubalgebra.coe_centralizer_centralizer]
    exact Set.centralizer_centralizer_centralizer ((S ∪ star S).centralizer)

def groupVonNeumannAlgebra (G : CountableDiscreteGroup.{u}) :
    VonNeumannAlgebra (GroupL2 G) :=
  vonNeumannClosure (Set.range fun g : G ↦
    (leftRegularRepresentation G g : GroupL2 G →L[ℂ] GroupL2 G))

abbrev GroupVonNeumannAlgebra (G : CountableDiscreteGroup.{u}) :=
  (groupVonNeumannAlgebra G).toStarSubalgebra

def delta (G : CountableDiscreteGroup.{u}) (g : G) : GroupL2 G :=
  by
    classical
    exact lp.single 2 g 1

def canonicalTrace (G : CountableDiscreteGroup.{u}) :
    GroupVonNeumannAlgebra G → ℂ :=
  fun x ↦ inner ℂ (delta G 1) ((x : GroupL2 G →L[ℂ] GroupL2 G) (delta G 1))

def ProjectionLE {A : Type u} [Mul A] (p q : A) : Prop :=
  p * q = p

def IsProjectionSupremum {A : Type u} [Mul A] [Star A]
    (S : Set A) (p : A) : Prop :=
  IsStarProjection p ∧
    (∀ q ∈ S, IsStarProjection q ∧ ProjectionLE q p) ∧
    ∀ r, IsStarProjection r → (∀ q ∈ S, ProjectionLE q r) → ProjectionLE p r

def IsNormalStarAlgEquiv
    {A : Type u} {B : Type v}
    [Semiring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
    [Semiring B] [StarRing B] [Algebra ℂ B] [StarModule ℂ B]
    (e : A ≃⋆ₐ[ℂ] B) : Prop :=
  (∀ (S : Set A) (p : A), IsProjectionSupremum S p →
    IsProjectionSupremum (e '' S) (e p)) ∧
  ∀ (S : Set B) (p : B), IsProjectionSupremum S p →
    IsProjectionSupremum (e.symm '' S) (e.symm p)

structure TracialGroupFactorEquiv
    (G : CountableDiscreteGroup.{u}) (H : CountableDiscreteGroup.{v}) where
  toStarAlgEquiv :
    GroupVonNeumannAlgebra G ≃⋆ₐ[ℂ] GroupVonNeumannAlgebra H
  normal : IsNormalStarAlgEquiv toStarAlgEquiv
  trace_preserving :
    ∀ x, canonicalTrace H (toStarAlgEquiv x) = canonicalTrace G x

def TracialGroupFactorsIsomorphic
    (G : CountableDiscreteGroup.{u}) (H : CountableDiscreteGroup.{v}) : Prop :=
  Nonempty (TracialGroupFactorEquiv G H)

end

end

section

universe u

theorem UnitaryRepresentation.hasAlmostInvariantUnitVectors_comp
    {G H K : Type u} [Group G] [Group H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (π : UnitaryRepresentation H K)
    (f : G →* H)
    (hπ : π.HasAlmostInvariantUnitVectors) :
    UnitaryRepresentation.HasAlmostInvariantUnitVectors (π.comp f) := by
  classical
  intro S ε hε

-- ===== paper groups Lambda / Gamma and family structures (lines 13690-14110) =====
    rw [map_mul]
    rfl

@[simp] theorem kDAction_toAdd (k : K) (d : Multiplicative D) :
    Multiplicative.toAdd (kDAction k d) = kDLinear k (Multiplicative.toAdd d) := rfl

abbrev Lambda := SemidirectProduct (Multiplicative D) K kDAction

instance : Countable Lambda := SemidirectProduct.equivProd.injective.countable

def lambdaGroup : ConnesRigidity.CountableDiscreteGroup where
  Carrier := Lambda
  group := inferInstance
  countable := inferInstance

@[simp] theorem Lambda_mul_right (g h : Lambda) :
    (g * h).right = g.right * h.right := rfl

abbrev lambdaInl : Multiplicative D →* Lambda := SemidirectProduct.inl

abbrev lambdaInr : K →* Lambda := SemidirectProduct.inr

abbrev lambdaProjection : Lambda →* K := SemidirectProduct.rightHom

@[simp] theorem lambdaProjection_inl (d : Multiplicative D) :
    lambdaProjection (lambdaInl d) = 1 := by
  exact SemidirectProduct.rightHom_inl d

@[simp] theorem lambdaProjection_inr (k : K) :
    lambdaProjection (lambdaInr k) = k := by
  exact SemidirectProduct.rightHom_inr k

set_option maxHeartbeats 800000 in

theorem lambda_conjugation (k : K) (d : Multiplicative D) :
    lambdaInl (kDAction k d) = lambdaInr k * lambdaInl d * (lambdaInr k)⁻¹ := by
  simpa only [map_inv] using (SemidirectProduct.inl_aut (φ := kDAction) k d)

end

section

open ConnesRigidity

universe u

structure GroupCardinalInvariant where
  carrier : CountableDiscreteGroup.{u} → Type u
  map_mulEquiv : ∀ {G H : CountableDiscreteGroup.{u}},
    (G ≃* H) → carrier G ≃ carrier H

namespace GroupCardinalInvariant

noncomputable def value (I : GroupCardinalInvariant.{u})
    (G : CountableDiscreteGroup.{u}) : ℕ :=
  Nat.card (I.carrier G)

theorem value_mulEquiv (I : GroupCardinalInvariant.{u})
    {G H : CountableDiscreteGroup.{u}} (e : G ≃* H) :
    I.value G = I.value H :=
  Nat.card_congr (I.map_mulEquiv e)

end GroupCardinalInvariant

theorem paperInvariantCard_injective {m n : ℕ}
    (h : 2 ^ (4 * m) = 2 ^ (4 * n)) : m = n := by
  have hmul : 4 * m = 4 * n :=
    Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ)) h
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < (4 : ℕ)) hmul

structure ExactIndexEmbedding
    (G H : CountableDiscreteGroup.{u}) (index : ℕ) where
  hom : G →* H
  injective : Function.Injective hom
  index_eq : hom.range.index = index

namespace ExactIndexEmbedding

variable {G H : CountableDiscreteGroup.{u}} {index : ℕ}

noncomputable def rangeEquiv (f : ExactIndexEmbedding G H index) :
    G ≃* f.hom.range :=
  MonoidHom.ofInjective f.injective

theorem range_finiteIndex (f : ExactIndexEmbedding G H index)
    (hindex : index ≠ 0) : f.hom.range.FiniteIndex :=
  Subgroup.finiteIndex_iff.mpr (by simpa [f.index_eq] using hindex)

end ExactIndexEmbedding

def AbstractlyCommensurable
    (G H : CountableDiscreteGroup.{u}) : Prop :=
  ∃ (S : Subgroup G) (T : Subgroup H),
    S.FiniteIndex ∧ T.FiniteIndex ∧ Nonempty (S ≃* T)

theorem abstractlyCommensurable_of_common_embedding
    {A G H : CountableDiscreteGroup.{u}} {i j : ℕ}
    (f : ExactIndexEmbedding A G i) (g : ExactIndexEmbedding A H j)
    (hi : i ≠ 0) (hj : j ≠ 0) :
    AbstractlyCommensurable G H := by
  refine ⟨f.hom.range, g.hom.range,
    f.range_finiteIndex hi, g.range_finiteIndex hj, ?_⟩
  exact ⟨f.rangeEquiv.symm.trans g.rangeEquiv⟩

theorem not_groupsIsomorphic_of_orderFour
    {G H : CountableDiscreteGroup.{u}}
    (hG : ∃ g : G, orderOf g = 4)
    (hH : ∀ h : H, orderOf h ≠ 4) :
    ¬GroupsIsomorphic G H := by
  rintro ⟨e⟩
  obtain ⟨g, hg⟩ := hG
  exact hH (e g) (by simpa using (e.orderOf_eq g).trans hg)

structure PaperFamilyInput where
  Lambda : CountableDiscreteGroup.{u}
  Gamma : ℕ → CountableDiscreteGroup.{u}
  invariant : GroupCardinalInvariant.{u}
  invariant_card : ∀ n, invariant.value (Gamma n) = 2 ^ (4 * n)
  lambda_no_order_four : ∀ g : Lambda, orderOf g ≠ 4
  gamma_order_four : ∀ n, ∃ g : Gamma n, orderOf g = 4
  lambda_fg : Group.FG Lambda
  gamma_fg : ∀ n, Group.FG (Gamma n)
  lambda_icc : IsICC Lambda
  gamma_icc : ∀ n, IsICC (Gamma n)
  lambda_propertyT : HasKazhdanPropertyT Lambda
  gamma_propertyT : ∀ n, HasKazhdanPropertyT (Gamma n)
  factors_isomorphic : ∀ n, TracialGroupFactorsIsomorphic (Gamma n) Lambda
  embeddings : ∀ n, ExactIndexEmbedding (Gamma 0) (Gamma n) (2 ^ (4 * n))

namespace PaperFamilyInput

variable (F : PaperFamilyInput.{u})

theorem parameter_eq_of_mulEquiv {m n : ℕ}
    (e : F.Gamma m ≃* F.Gamma n) : m = n := by
  apply paperInvariantCard_injective
  calc
    2 ^ (4 * m) = F.invariant.value (F.Gamma m) :=
      (F.invariant_card m).symm
    _ = F.invariant.value (F.Gamma n) := F.invariant.value_mulEquiv e
    _ = 2 ^ (4 * n) := F.invariant_card n

theorem gamma_not_isomorphic {m n : ℕ} (hmn : m ≠ n) :
    ¬GroupsIsomorphic (F.Gamma m) (F.Gamma n) := by
  rintro ⟨e⟩
  exact hmn (F.parameter_eq_of_mulEquiv e)

theorem gamma_not_isomorphic_lambda (n : ℕ) :
    ¬GroupsIsomorphic (F.Gamma n) F.Lambda :=
  not_groupsIsomorphic_of_orderFour (F.gamma_order_four n)
    F.lambda_no_order_four

theorem lambda_not_isomorphic_gamma (n : ℕ) :
    ¬GroupsIsomorphic F.Lambda (F.Gamma n) := by
  rintro ⟨e⟩
  exact F.gamma_not_isomorphic_lambda n ⟨e.symm⟩

theorem gamma_commensurable (m n : ℕ) :
    AbstractlyCommensurable (F.Gamma m) (F.Gamma n) := by
  apply abstractlyCommensurable_of_common_embedding
    (F.embeddings m) (F.embeddings n)
  · exact pow_ne_zero _ (by decide : (2 : ℕ) ≠ 0)
  · exact pow_ne_zero _ (by decide : (2 : ℕ) ≠ 0)

end PaperFamilyInput

structure InfinitePropertyTFiber where
  Lambda : CountableDiscreteGroup.{u}
  Gamma : ℕ → CountableDiscreteGroup.{u}
  lambda_fg : Group.FG Lambda
  gamma_fg : ∀ n, Group.FG (Gamma n)
  lambda_icc : IsICC Lambda
  gamma_icc : ∀ n, IsICC (Gamma n)
  lambda_propertyT : HasKazhdanPropertyT Lambda
  gamma_propertyT : ∀ n, HasKazhdanPropertyT (Gamma n)
  factors_isomorphic : ∀ n, TracialGroupFactorsIsomorphic (Gamma n) Lambda
  gamma_pairwise_nonisomorphic : ∀ {m n}, m ≠ n →
    ¬GroupsIsomorphic (Gamma m) (Gamma n)
  lambda_not_isomorphic : ∀ n, ¬GroupsIsomorphic Lambda (Gamma n)
  exact_index_embeddings :
    ∀ n, ExactIndexEmbedding (Gamma 0) (Gamma n) (2 ^ (4 * n))
  commensurable : ∀ m n, AbstractlyCommensurable (Gamma m) (Gamma n)

def PaperFamilyInput.toInfinitePropertyTFiber (F : PaperFamilyInput.{u}) :
    InfinitePropertyTFiber.{u} where
  Lambda := F.Lambda
  Gamma := F.Gamma
  lambda_fg := F.lambda_fg
  gamma_fg := F.gamma_fg
  lambda_icc := F.lambda_icc
  gamma_icc := F.gamma_icc
  lambda_propertyT := F.lambda_propertyT
  gamma_propertyT := F.gamma_propertyT
  factors_isomorphic := F.factors_isomorphic
  gamma_pairwise_nonisomorphic := fun hmn => F.gamma_not_isomorphic hmn
  lambda_not_isomorphic := F.lambda_not_isomorphic_gamma
  exact_index_embeddings := F.embeddings
  commensurable := F.gamma_commensurable

end

noncomputable section

open ConnesRigidity

def kXLinear : K →* (X ≃ₗ[F] X) where
  toFun k := LinearEquiv.dualMap (kLinear k⁻¹)
  map_one' := by
    apply LinearEquiv.ext
    intro ℓ
    apply LinearMap.ext
    intro v
    simp
  map_mul' k h := by
    apply LinearEquiv.ext
    intro ℓ
    apply LinearMap.ext
    intro v
    simp [map_mul]

@[simp] theorem kXLinear_apply (k : K) (ℓ : X) (v : V) :
    kXLinear k ℓ v = ℓ (kLinear k⁻¹ v) := rfl

def kYLinear : K →* (Y ≃ₗ[F] Y) where
  toFun k := LinearEquiv.dualMap (kDividedSquareLinear k⁻¹)
  map_one' := by
    apply LinearEquiv.ext
    intro q
    apply LinearMap.ext
    intro b
    simp
  map_mul' k h := by
    apply LinearEquiv.ext
    intro q
    apply LinearMap.ext
    intro b
    simp [map_mul]

@[simp] theorem kYLinear_apply (k : K) (q : Y) (b : B) :
    kYLinear k q b = q (kDividedSquareLinear k⁻¹ b) := rfl

theorem continuous_kXLinear (k : K) :
    Continuous (kXLinear k : X → X) := by
  change Continuous
    (fun ℓ : X => ℓ.comp (kLinear k⁻¹).toLinearMap)
  exact continuous_X_precomp (kLinear k⁻¹).toLinearMap

theorem continuous_kYLinear (k : K) :
    Continuous (kYLinear k : Y → Y) := by
  change Continuous
    (fun q : Y => q.comp (kDividedSquareLinear k⁻¹).toLinearMap)
  exact continuous_Y_precomp (kDividedSquareLinear k⁻¹).toLinearMap

theorem kLinear_shiftVector (k : K) (n : ℕ) (v : V) :
    kLinear k (shiftVector n v) = shiftVector n (kLinear k v) := by
  simp only [kLinear_apply, shiftVector, LinearMap.restrictScalars_apply,
    LinearMap.lsmul_apply]
  exact (Matrix.SpecialLinearGroup.toLin' (pi₂ k)).map_smul _ _

theorem kXLinear_shift (k : K) (n : ℕ) (ℓ : X) :
    shift n (kXLinear k ℓ) = kXLinear k (shift n ℓ) := by
  apply LinearMap.ext
  intro v
  change ℓ (kLinear k⁻¹ (shiftVector n v)) =
    ℓ (shiftVector n (kLinear k⁻¹ v))
  rw [kLinear_shiftVector]

theorem kYLinear_carry (k : K) (ℓ ℓ' : X) :
    kYLinear k (carry ℓ ℓ') =
      carry (kXLinear k ℓ) (kXLinear k ℓ') := by
  apply linearMap_ext_on_diagonal
  intro v
  change carry ℓ ℓ' (kDividedSquareLinear k⁻¹ (diagonal v)) =
    carry (kXLinear k ℓ) (kXLinear k ℓ') (diagonal v)
  rw [kDividedSquareLinear_diagonal]
  simp only [carry_apply_diagonal, kXLinear_apply]

theorem kYLinear_shiftedCarry (k : K) (n : ℕ) (ℓ ℓ' : X) :
    kYLinear k (shiftedCarry n ℓ ℓ') =
      shiftedCarry n (kXLinear k ℓ) (kXLinear k ℓ') := by
  unfold shiftedCarry
  rw [kYLinear_carry, ← kXLinear_shift, ← kXLinear_shift]

def kCarryAddAut (n : ℕ) (k : K) : AddAut (CarryGroup n) where
  toFun z := ⟨kXLinear k z.linear, kYLinear k z.quadratic⟩
  invFun z := ⟨kXLinear k⁻¹ z.linear, kYLinear k⁻¹ z.quadratic⟩
  left_inv z := by
    apply CarryGroup.ext <;> simp
  right_inv z := by
    apply CarryGroup.ext <;> simp
  map_add' z w := by
    apply CarryGroup.ext
    · simp
    · change kYLinear k
        (z.quadratic + w.quadratic + shiftedCarry n z.linear w.linear) =
          kYLinear k z.quadratic + kYLinear k w.quadratic +
            shiftedCarry n (kXLinear k z.linear) (kXLinear k w.linear)
      rw [map_add, map_add, kYLinear_shiftedCarry]

@[simp] theorem kCarryAddAut_linear (n : ℕ) (k : K) (z : CarryGroup n) :
    (kCarryAddAut n k z).linear = kXLinear k z.linear := rfl

@[simp] theorem kCarryAddAut_quadratic (n : ℕ) (k : K) (z : CarryGroup n) :
    (kCarryAddAut n k z).quadratic = kYLinear k z.quadratic := rfl

def kCarryAction (n : ℕ) : K →* MulAut (Multiplicative (CarryGroup n)) where
  toFun k := AddEquiv.toMultiplicative (kCarryAddAut n k)
  map_one' := by
    apply MulEquiv.ext
    intro z
    apply Multiplicative.toAdd.injective
    apply CarryGroup.ext
    · change kXLinear 1 (Multiplicative.toAdd z).linear =
        (Multiplicative.toAdd z).linear
      simp
    · change kYLinear 1 (Multiplicative.toAdd z).quadratic =
        (Multiplicative.toAdd z).quadratic
      simp
  map_mul' k h := by
    apply MulEquiv.ext
    intro z
    apply Multiplicative.toAdd.injective
    apply CarryGroup.ext
    · change kXLinear (k * h) (Multiplicative.toAdd z).linear =
        kXLinear k (kXLinear h (Multiplicative.toAdd z).linear)
      rw [map_mul]
      rfl
    · change kYLinear (k * h) (Multiplicative.toAdd z).quadratic =
        kYLinear k (kYLinear h (Multiplicative.toAdd z).quadratic)
      rw [map_mul]
      rfl

@[simp] theorem kCarryAction_linear (n : ℕ) (k : K)
    (z : Multiplicative (CarryGroup n)) :
    (Multiplicative.toAdd (kCarryAction n k z)).linear =
      kXLinear k (Multiplicative.toAdd z).linear := rfl

@[simp] theorem kCarryAction_quadratic (n : ℕ) (k : K)
    (z : Multiplicative (CarryGroup n)) :
    (Multiplicative.toAdd (kCarryAction n k z)).quadratic =
      kYLinear k (Multiplicative.toAdd z).quadratic := rfl

theorem continuous_kCarryAddAut (n : ℕ) (k : K) :
    Continuous (kCarryAddAut n k : CarryGroup n → CarryGroup n) := by
  apply continuous_CarryGroup_iff.mpr
  constructor
  · intro v
    exact continuous_linear_eval n (kLinear k⁻¹ v)
  · intro b
    exact continuous_quadratic_eval n (kDividedSquareLinear k⁻¹ b)

theorem continuous_kCarryAction (n : ℕ) (k : K) :
    Continuous (kCarryAction n k :
      Multiplicative (CarryGroup n) → Multiplicative (CarryGroup n)) := by
  change Continuous
    (fun z : CarryGroup n => kCarryAddAut n k z)
  exact continuous_kCarryAddAut n k

def kEAction (n : ℕ) : K →* MulAut (Multiplicative (E n)) := by
  change K →* MulAut (PontryaginDual (Multiplicative (CarryGroup n)))
  exact dualAction (Multiplicative (CarryGroup n)) K (kCarryAction n)
    (continuous_kCarryAction n)

@[simp] theorem kEAction_apply (n : ℕ) (k : K)
    (η : Multiplicative (E n)) (z : Multiplicative (CarryGroup n)) :
    (kEAction n k η : PontryaginDual (Multiplicative (CarryGroup n))) z =
      (η : PontryaginDual (Multiplicative (CarryGroup n)))
        ((kCarryAction n k)⁻¹ z) := rfl

noncomputable instance instMultiplicativeECountable (n : ℕ) :
    Countable (Multiplicative (E n)) :=
  (Multiplicative.toAdd : Multiplicative (E n) ≃ E n).injective.countable

abbrev Gamma (n : ℕ) :=
  SemidirectProduct (Multiplicative (E n)) K (kEAction n)

noncomputable instance instGammaCountable (n : ℕ) : Countable (Gamma n) :=
  SemidirectProduct.equivProd.injective.countable

def gammaGroup (n : ℕ) : CountableDiscreteGroup where
  Carrier := Gamma n
  group := inferInstance
  countable := inferInstance

def gammaOrderFourElement (n : ℕ) : Gamma n :=
  SemidirectProduct.inl (Multiplicative.ofAdd (epsilon n e))

theorem gammaOrderFourElement_orderOf (n : ℕ) :
    orderOf (gammaOrderFourElement n) = 4 := by
  rw [gammaOrderFourElement,
    orderOf_injective (SemidirectProduct.inl :
      Multiplicative (E n) →* Gamma n) SemidirectProduct.inl_injective]
  exact epsilon_addOrderOf n

theorem gamma_has_order_four (n : ℕ) :
    ∃ g : gammaGroup n, orderOf g = 4 :=
  ⟨gammaOrderFourElement n, gammaOrderFourElement_orderOf n⟩

end

section

open ConnesRigidity MeasureTheory

noncomputable section

def paperSplitAddAut (k : K) : (X × Y) ≃+ (X × Y) :=
  (kXLinear k).toAddEquiv.prodCongr (kYLinear k).toAddEquiv

@[simp] theorem paperSplitAddAut_apply (k : K) (z : X × Y) :
    paperSplitAddAut k z = (kXLinear k z.1, kYLinear k z.2) := rfl

def paperSplitPerm : K →* Equiv.Perm (X × Y) where
  toFun k := (paperSplitAddAut k).toEquiv
  map_one' := by
    apply Equiv.ext
    intro z
    change (kXLinear 1 z.1, kYLinear 1 z.2) = z
    simp
  map_mul' k h := by
    apply Equiv.ext

-- ===== PaperAnalyticInput and assembly (lines 36840-36952) =====
  calc
    2 ^ (4 * m) = paperGroupCardinalInvariant.value (gammaGroup m) :=
      (paperInvariant_card m).symm
    _ = paperGroupCardinalInvariant.value (gammaGroup n) :=
      paperGroupCardinalInvariant.value_mulEquiv f
    _ = 2 ^ (4 * n) := paperInvariant_card n

theorem gamma_pairwise_nonisomorphic {m n : ℕ} (hmn : m ≠ n) :
    ¬GroupsIsomorphic (gammaGroup m) (gammaGroup n) := by
  rintro ⟨f⟩
  exact hmn (gamma_parameter_eq_of_mulEquiv f)

structure PaperAnalyticInput where
  suslinRelative : SuslinRelativeElementaryGeneration

theorem paperLambda_hasNoOrderFour : HasNoOrderFour Lambda := by
  change HasNoOrderFour (SemidirectProduct (Multiplicative D) K kDAction)
  apply semidirect_hasNoOrderFour_of_no_nontrivial_torsion_of_exponentTwo
    (N := Multiplicative D) (Q := K) kDAction K_no_nontrivial_torsion
  intro d
  rw [pow_two]
  apply Multiplicative.toAdd.injective
  change Multiplicative.toAdd d + Multiplicative.toAdd d = 0
  exact D_add_self _

theorem paperLambda_orderOf_ne_four (g : lambdaGroup) : orderOf g ≠ 4 := by
  intro hg
  obtain ⟨hfour, htwo⟩ := (orderOf_eq_four_iff g).mp hg
  exact htwo (paperLambda_hasNoOrderFour g hfour)

def paperFamilyInput_of_universalLattice
    (hUniversal : ErshovJaikinUniversalLatticePropertyT) :
    PaperFamilyInput where
  Lambda := lambdaGroup
  Gamma := gammaGroup
  invariant := paperGroupCardinalInvariant
  invariant_card := paperInvariant_card
  lambda_no_order_four := paperLambda_orderOf_ne_four
  gamma_order_four := gamma_has_order_four
  lambda_fg := hasKazhdanPropertyT_finitelyGenerated lambdaGroup
    (lambda_hasKazhdanPropertyT_unconditional hUniversal)
  gamma_fg n := hasKazhdanPropertyT_finitelyGenerated (gammaGroup n)
    (gamma_hasKazhdanPropertyT_unconditional n hUniversal)
  lambda_icc := lambda_isICC
  gamma_icc := gamma_isICC
  lambda_propertyT := lambda_hasKazhdanPropertyT_unconditional hUniversal
  gamma_propertyT n := gamma_hasKazhdanPropertyT_unconditional n hUniversal
  factors_isomorphic := paper_factors_isomorphic
  embeddings := gammaExactIndexEmbedding

namespace PaperAnalyticInput

theorem universalLattice (input : PaperAnalyticInput) :
    ErshovJaikinUniversalLatticePropertyT :=
  universalLatticePropertyT_of_suslinRelative input.suslinRelative

theorem lambda_propertyT (input : PaperAnalyticInput) :
    HasKazhdanPropertyT lambdaGroup :=
  lambda_hasKazhdanPropertyT_unconditional input.universalLattice

theorem gamma_propertyT (input : PaperAnalyticInput) (n : ℕ) :
    HasKazhdanPropertyT (gammaGroup n) :=
  gamma_hasKazhdanPropertyT_unconditional n input.universalLattice

theorem lambda_icc : IsICC lambdaGroup :=
  lambda_isICC

theorem gamma_icc (n : ℕ) : IsICC (gammaGroup n) :=
  gamma_isICC n

theorem gamma_not_isomorphic_lambda (n : ℕ) :
    ¬GroupsIsomorphic (gammaGroup n) lambdaGroup :=
  not_groupsIsomorphic_of_orderFour (gamma_has_order_four n)
    paperLambda_orderOf_ne_four

def toPaperFamilyInput (input : PaperAnalyticInput) :
    PaperFamilyInput :=
  paperFamilyInput_of_universalLattice input.universalLattice

@[simp] theorem toPaperFamilyInput_lambda
    (input : PaperAnalyticInput) :
    input.toPaperFamilyInput.Lambda = lambdaGroup := rfl

@[simp] theorem toPaperFamilyInput_gamma
    (input : PaperAnalyticInput) (n : ℕ) :
    input.toPaperFamilyInput.Gamma n = gammaGroup n := rfl

def infinitePropertyTFiber (input : PaperAnalyticInput) :
    InfinitePropertyTFiber :=
  input.toPaperFamilyInput.toInfinitePropertyTFiber

@[simp] theorem infinitePropertyTFiber_lambda
    (input : PaperAnalyticInput) :
    input.infinitePropertyTFiber.Lambda = lambdaGroup := rfl

@[simp] theorem infinitePropertyTFiber_gamma
    (input : PaperAnalyticInput) (n : ℕ) :
    input.infinitePropertyTFiber.Gamma n = gammaGroup n := rfl

end PaperAnalyticInput

theorem paperAnalyticInput : PaperAnalyticInput :=
  ⟨suslinRelativeElementaryGeneration⟩

def paperInfinitePropertyTFiber : InfinitePropertyTFiber :=
  paperAnalyticInput.infinitePropertyTFiber

end

noncomputable section

def manuscriptInfinitePropertyTFiber : InfinitePropertyTFiber :=
  paperInfinitePropertyTFiber

-- ===== main pair theorem (abridged) =====
theorem exists_nonisomorphic_propertyT_icc_groups_with_isomorphic_factors :
    ∃ Γ Λ : ConnesRigidity.CountableDiscreteGroup.{0},
      Group.FG Γ ∧ Group.FG Λ ∧
      ConnesRigidity.IsICC Γ ∧
      ConnesRigidity.HasKazhdanPropertyT Γ ∧
      ConnesRigidity.IsICC Λ ∧
      ConnesRigidity.HasKazhdanPropertyT Λ ∧
      ConnesRigidity.TracialGroupFactorsIsomorphic Γ Λ ∧
      ¬ConnesRigidity.GroupsIsomorphic Γ Λ := by
  -- (long `let _ := ...` warm-up block omitted)
  let F := manuscriptInfinitePropertyTFiber
  refine ⟨F.Gamma 0, F.Lambda, F.gamma_fg 0, F.lambda_fg,
    F.gamma_icc 0, F.gamma_propertyT 0, F.lambda_icc,
    F.lambda_propertyT, F.factors_isomorphic 0, ?_⟩
  rintro ⟨e⟩
  exact F.lambda_not_isomorphic 0 ⟨e.symm⟩


-- ===== infinite family theorem (lines 37347-37374) =====
theorem
    exists_infinite_pairwise_nonisomorphic_propertyT_icc_groups_with_isomorphic_factors :
    ∃ (Λ : ConnesRigidity.CountableDiscreteGroup.{0})
      (Γ : ℕ → ConnesRigidity.CountableDiscreteGroup.{0}),
      Group.FG Λ ∧
      (∀ n, Group.FG (Γ n)) ∧
      ConnesRigidity.IsICC Λ ∧
      (∀ n, ConnesRigidity.IsICC (Γ n)) ∧
      ConnesRigidity.HasKazhdanPropertyT Λ ∧
      (∀ n, ConnesRigidity.HasKazhdanPropertyT (Γ n)) ∧
      (∀ n, ConnesRigidity.TracialGroupFactorsIsomorphic (Γ n) Λ) ∧
      (∀ m n, ConnesRigidity.TracialGroupFactorsIsomorphic (Γ m) (Γ n)) ∧
      (∀ ⦃m n : ℕ⦄, m ≠ n →
        ¬ConnesRigidity.GroupsIsomorphic (Γ m) (Γ n)) ∧
      (∀ n, ¬ConnesRigidity.GroupsIsomorphic Λ (Γ n)) := by
  let F := manuscriptInfinitePropertyTFiber
  refine ⟨F.Lambda, F.Gamma, F.lambda_fg, F.gamma_fg,
    F.lambda_icc, F.gamma_icc, F.lambda_propertyT, F.gamma_propertyT,
    F.factors_isomorphic, ?_, ?_, F.lambda_not_isomorphic⟩
  · intro m n
    exact groupFactorsIsomorphic_trans (F.factors_isomorphic m)
      (groupFactorsIsomorphic_symm (F.factors_isomorphic n))
  · intro m n hmn
    exact F.gamma_pairwise_nonisomorphic hmn

end

end ConnesRigidity