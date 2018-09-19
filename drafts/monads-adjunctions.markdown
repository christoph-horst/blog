---
title: Monads from adjunctions, adjunctions from monads.
date: 2018-08-09
---
<div style="display:none;">
$$\newcommand{cat}{\mathsf}%
\newcommand{id}{\mathrm{id}}%
\newcommand{bind}{\mathbin{\mathrm{\gg=}}}%
\newcommand{hom}{\mathrm{hom}}%
\newcommand{natto}{\Rightarrow}%{\stackrel{\bullet}{\to}}%
\newcommand{Id}{\mathrm{Id}}%
$$
</div>
There is a tight relationship between monads and adjunctions. In fact,
it is easy to see that every pair of adjoint functors yields a
monad. What is really interesting is that conversely, every monad
arises by some adjunction.

Let's look at an example first. Fix a set $S$, then there is a natural
bijection of hom-sets in the category $\cat{Set}$:

$$c: \hom(X\times S, Y)\xrightarrow{\cong}\hom(X, \hom(S, Y)),$$

known as "currying". It sends a function $f : X\times S\to Y$ to a
"curried" function $c(f) : X\to \hom(S, Y)$ defined by $c(f)(x) =
s\mapsto f(x,s)$. This can be interpreted as an adjunction, where
$-\times S$ is the left adjoint and $\hom(S, -)$ is the right
adjoint. The composition of these functors is the functor $X\mapsto
\hom(S, X\times S)$, which you might recognize as the `State`
monad.

# Adjoint functors

We recall the definition of an adjoint pair of functors and some
properties (without proof.) Let $C$, $D$ be categories, $F: C\to D$
and $G: D\to C$ be functors. Then $F$, $G$ is called an *adjoint pair*
if there is a natural bijection

$$\Phi_{XY} : \hom_D(FX, Y)\xrightarrow{\cong}\hom_C(X, GY).$$

We call $F$ the *left-adjoint* and $G$ the *right-adjoint*, and we
write $F\dashv G$.

An adjunction comes with natural transformations, $\eta: G\circ F\natto\Id$,
the *unit* of the adjunction, and $\varepsilon: \Id\natto F\circ G$, the
*counit*. These arise as follows:

$$\eta_X = \Phi_{X,FX}(\id_{FX}) : X\to GFX,$$

$$\varepsilon_Y = \Phi_{GY,Y}^{-1}(\id_{GY}) : FGY\to Y,$$

and they satisy so-called triangle equations given by the following
commuting diagrams:

$$\require{AMScd}
\begin{CD}
F\circ\Id_C @>{F\bullet\eta}>> F\circ G\circ F\\
@| @V{\varepsilon\bullet F}VV\\
F @= \Id_D\circ F
\end{CD}$$

$$\begin{CD}
\Id_C\circ G @>{\eta\bullet G}>> G\circ F\circ G\\
@| @V{G\bullet \varepsilon}VV\\
G @= G\circ \Id_D
\end{CD}$$

(Forgive me if these don't show up as actual triangles due to
technical limitations.)

It will come in handy later to write $\Phi$ in terms of $\eta$ and
$\varepsilon$:

$$\begin{align*}
\Phi_{XY}(f : FX\to Y) &= G(f)\circ\eta_X &: X \xrightarrow{\eta_X} GFX \xrightarrow{Gf} GY\\
\Phi^{-1}_{XY}(g :X\to GY) &= \varepsilon_Y\circ F(g) &: FX \xrightarrow{Fg} FGY \xrightarrow{\varepsilon_Y} Y
\end{align*}$$

# Monads from adjunctions

When we post-compose the first triangle diagram with $G$ and pre-compose
the second with $F$, we obtain a very familiar diagram:

$$\begin{CD}
\Id_C\circ GF @>{\eta\bullet GF}>> GFGF @<{GF\bullet\eta}<< GF\circ\Id_C\\
@| @V{G\bullet\varepsilon\bullet F}VV @|\\
GF @= GF @= GF
\end{CD}$$

Set $M := G\circ F$ and $\mu := G\bullet\varepsilon\bullet F$. We obtain the following diagram:

$$\begin{CD}
\Id_C\circ M @>{\eta\bullet M}>> M\circ M @<{M\bullet \eta}<< M\circ\Id_C\\
@| @V{\mu}VV @| \\
M @= M @= M
\end{CD}$$

This ist just the diagram for the left and right identities for
monads! To see that associativity holds, first recall the horizontal
composition $\varepsilon\bullet\varepsilon : FGFG\natto\Id_D$. It was
defined as the diagonal of this commuting diagram:

$$\begin{CD}
FGFG @>{FG\bullet\varepsilon}>> FG\circ\Id_D\\
@V{\varepsilon\bullet FG}VV  @V{\varepsilon\bullet\Id_D}VV\\
\Id_D\circ FG @>{\Id_D\bullet\varepsilon}>> \Id_D\circ\Id_D
\end{CD}$$

Post-compose with $G$ and pre-compose with $F$, similar to what we did before:

$$\begin{CD}
GFGFGF    @>{GFG\bullet\varepsilon\bullet F}>>                GFGF\\
@V{G\bullet\varepsilon\bullet FGF}VV         @V{G\bullet\varepsilon \bullet F}VV\\
GFGF      @>{G\bullet\varepsilon\bullet F}>>                   GF
\end{CD}
\quad
\sim
\quad
\begin{CD}MMM     @>{M\bullet\mu}>>        MM\\
@V{\mu\bullet M}VV                        @V{\mu}VV\\
MM                     @>{\mu}>>            M
\end{CD}$$

This is exactly the associativity diagram we need.

Conclusion so far: Every adjunction yields a monad.

There's a dual statement included that I won't go into in this
article. Every adjunction also yields a comonad $W = F\circ G$, with the
given $\varepsilon: \Id\natto W$ and $\Delta = F\bullet\eta\bullet G :
W\natto W\circ W$.

Let's see about the converse statement. Does every monad come from an
adjunction? 

# Adjunctions from monads

There are two very different canonical ways to find an adjoint pair
that form a monad. In the following, let $(M,\eta,\mu)$ be a monad in
a category $C$.

## The Kleisli category

Let $C_M$ be the category whose objects are exactly the objects of
$C$, and whose arrows from $X$ to $Y$ are exactly the $C$-morphisms
$X\to MY$. To avoid confusion, we're going to write $X\to_M Y$ for
the arrows in $C_M$ and $X\to Y$ for arrows in $C$.

Given arrows $f: X\to MY$, $g: Y\to MZ$, an arrow $g\circ_M f:
X\to MZ$ is given by the *Kleisli composition*, $g\circ_M f :=
\mu_Z\circ M(g)\circ f$.

$$ g\circ_M f := X\stackrel{f}\longrightarrow
MY\stackrel{M(g)}{\longrightarrow} MMZ\stackrel{\mu_Z}{\to} MZ$$

We check that this results in a lawful composition.

1. $\eta_Y\circ_M f = \mu_Y\circ M(\eta_Y)\circ f = f$, because
$\mu\circ(M\bullet\eta) = \id_M$ (this is, perhaps confusingly, the
_right_ identity law for monads.)

2. $f\circ_M\eta_X = \mu_Y\circ M(f)\circ\eta_X =
\mu_Y\circ\eta_{MY}\circ f = f$ by naturality and because
$\mu\circ(\eta\bullet M) =\id_M$ (this is the _left_ identity law.)

3. Let $h: Z\to_M W$ be another arrow. Then

$$
\begin{align*}
h\circ_M(g\circ_M f) &= h\circ_M(\mu_Z\circ M(g)\circ f)\\
&= \mu_W\circ \underline{M(h) \circ \mu_Z}\circ M(g)\circ f\\
&= \underline{\mu_W\circ\mu_{MW}}\circ MM(h)\circ M(g)\circ f\\
&= \mu_W\circ M(\mu_W)\circ MM(h)\circ M(g)\circ f\\
&= \mu_W\circ M(\mu_W\circ M(h)\circ g)\circ f\\
&= (h\circ_M g)\circ_M f,\end{align*}
$$

by naturality and the associative law of monads.

We see that, indeed, $C_M$ is a category, where the composition is
given by $\circ_M$, and the identity associated with an object $X$ is
$\eta_X$. This category is called the *Kleisli category* of $M$.

The Kleisli composition is often written an operator like `<=<`,
there's a flipped form `>=>` called the "Kleisli fish".

## The Kleisli adjunction

Let's introduce two functors, $F_M: C\to C_M$ and $G_M: C_M\to C$. On
objects, $F_M$ maps each object to itself (recall that the objects of
$C_M$ are precisely the objects of $C$). Then $F_M$ must send a
morphism $f: X\to Y$ to a $C_M$-morphism $F_M(f) : X\to_M Y$, that is, a
$C$-morphism $X\to MY$. We can accomplish that by post-composing
with an $\eta$, so we have $F_M(f) := \eta_Y \circ f: X\to MY$.

$f: X\to Y\quad\leadsto\quad F_M(f): X\xrightarrow{f} Y\xrightarrow{\eta_Y} MY$

The other functor, $G_M$, can't simply undo this, because there's no
general way to obtain a morphism $X\to Y$ from $X\to MY$. We cannot
"unpack" monads, but we can "flatten" using $\mu$. So we define $G_M(X)
= M(X)$ on objects, and $G_M(f: X\to MY) := \mu_Y \circ M(f)$.

$f: X\to M(Y)\quad\leadsto\quad G_M(f): M(X)\xrightarrow{M(f)}
MM(Y)\xrightarrow{\mu_Y} M(Y)$.

To show that they are adjoint, observe that a $C$-morphism $f: X\to
MY$ is simultaneously a morphism $X\to_M Y$ in $C_M$, so with our
functors, it's $F_M(X)\to_M Y$ and $X\to G_M(Y)$ at the same time. This
means that the hom-set bijection is actually an identity.

$$\begin{align*}
(\Phi_M)_{XY} : \hom_{C_M}(F_M(X), Y) &\xrightarrow{\cong} \hom_C(X, G(Y))\\
f&\mapsto f
\end{align*}$$

What could be more natural than an identity? But not so fast, let's do
this carefully. First, let $f: T\to X$ be a morphism in $C$. Then
$\hom_{C_M}(F_M(f), Y)$ is precomposition with $F_M(f)$, that is, for
$\varphi \in\hom_{C_M}(F_M(X), Y)$, we have

$$
\begin{align*}
\hom_{C_M}(F_M(f), Y)(\varphi) &= \varphi\circ_M F_M(f)\\
&= \mu_Y\circ M(\varphi)\circ\eta_X\circ f \\
&= \mu_Y\circ\eta_{MY}\circ\varphi\circ f\\
&= \varphi\circ f\\
&= \hom_C(f, G_M(Y))(\varphi)
\end{align*}
$$

by naturality of $\eta$ and the left identity law. For the other
variable things are much easier, with $g: Y\to_M T$,
$\hom_{C_M}(F_M(X), g)(\varphi) = g\circ_M\varphi = \mu_T\circ
M(g)\circ\varphi = \hom_C(X, G_M(g))(\varphi)$ for
$\varphi\in\hom_{C_M}(X, Y)$.

## Eilenberg-Moore algebras

An $M$-algebra (also called an Eilenberg-Moore algebra) is a pair $(X,
h)$ of an object $X\in C$ and an arrow $h: MX\to X$, such that the
following diagrams commute:

$$
\begin{CD}
MMX   @>{Mh}>>   MX \\
@V{\mu_X}VV @V{h}VV\\
MX   @>{h}>>     X
\end{CD}$$

and

$$\begin{CD}
X @>{\eta_X}>> MX\\
@| @V{h}VV\\
X @= X
\end{CD}$$

A morphism between two $M$-algebras, $(X, f: MX\to X)$ and $(Y, g:
MY\to Y)$ is a $C$-morphism $h: X\to Y$ which is compatible with the two
algebras in the sense that the following diagram commutes:

$$\begin{CD}
MX @>{f}>> X\\
@V{Mh}VV  @V{h}VV \\
MY @>{g}>> Y
\end{CD}$$

(One could also say that a morphism of $M$-algebras _is_ a diagram
like this.) The morphisms compose in an obvious way and we have the
obvious identities, so $C^M$ is a category, the *Eilenberg-Moore
category* of $M$.

### Some examples

In general, it is not clear for a given object $X\in C$ that an
$M$-algebra $MX\to X$ even exists. For a simple example, if $M$ is the
`Maybe` monad, then there does not exist an $M$-algebra $h:
M(\emptyset)\to\emptyset$, because $h(\mathsf{Nothing})\in\emptyset$
is a contradiction. It turns out that there is a 1:1 correspondence in
this case between $M$-algebras $h: MX\to X$ and *pointed sets* $(X,
x_0\in X)$ via

$$h(x) = \begin{cases}x\text{ if }x\in X\\x_0\text{ if
}x = \mathsf{Nothing}\end{cases}.$$

($h$ must send everything in $X$ to
itself due to the condition $h\circ\eta_X = \id_X$.)

If we take the list monad $L$, then there is a 1:1 correspondence
between $L$-algebras $h: LX\to X$ and monoids $(X,\diamond, e)$, by
$h([x_1, \ldots, x_n]) = x_1\diamond\cdots\diamond x_n$.

Interestingly, the list functor is the free functor to monoids, and
the maybe functor is the free functor to pointed sets. I'm sure this
isn't an accident.

## The Eilenberg-Moore adjunction

Let's again define a pair of functors, $F^M: C\to C^M$ and $G^M: C^M\to
C$. The functor $F^M$ must send an object $X\in C$ to an $M$-algebra,
preferably one that is somehow connected with $X$. But this is
difficult in general, as the previous section showed. Fortunately,
there is a canonical choice just one more $M$ away: $\mu_X : MMX\to MX$
automatically satisfies the conditions for an $M$-algebra, so we set
$F^M(X) = (MX, \mu_X)$, the required conditions

$$\begin{CD}
MX  @>{\eta_{MX}}>> MMX\\
@|                 @V{\mu_X}VV\\
MX @=              MX
\end{CD}$$

and

$$\begin{CD}
MMMX   @>{M\mu_X}>>   MMX\\
@V{\mu_{MX}}VV    @V{\mu_X}VV\\
MMX    @>{\mu_X}>>    MX
\end{CD}$$

come from the left identity and the associativity condition of the
monad $M$.

A $C$-morphism $f: X\to Y$ must then be sent to a morphism $F^M(f):
(MX, \mu_X)\to(MY, \mu_Y)$, we set $F^M(f) = M(f)$:

$$
f : X\to Y
\quad\leadsto\quad
\begin{CD}
MMX   @>{\mu_X}>> MX\\
@V{MM(f)}VV      @V{M(f)}VV\\
MMY   @>{\mu_Y}>> MY
\end{CD}$$

By naturality of $\mu$, this diagram always commutes.

The functor $G^M$ is simpler, an object $(X, f: MX\to X)$ is sent to
$X$, a morphism $h: (X, f: MX\to X)\to(Y, g:MY\to Y)$ is sent to the
arrow $h: X\to Y$. So $G^M$ is like a _forgetful_ functor, it simply
forgets structure.

We now construct a bijection

$$\Phi^M_{X,(Y,g)}: \hom_{C^M}(F^MX, (Y,g))\xrightarrow{\cong}\hom_C(X,G^M(Y,g))$$

Let $h: F^MX=(MX, \mu_X) \to (Y,g)$ be a morphism in $C^M$. We ignore
the compatibility condition and just focus on the part $h: MX\to Y$.
By precomposing with $\eta_X$, we obtain a morphism $X\to Y$, or $X\to
G^M(Y,g)$, so we can set $\Phi^M(h) = h\circ\eta_X$.

$$\Phi^M_{X, (Y,g)}\left (
\begin{CD}
MMX @>{\mu_X}>> MX\\
@V{Mh}VV        @V{h}VV\\
MY @>{g}>>      Y
\end{CD}
\right ) = \begin{CD} X @>{\eta_X}>> MX @>{h}>> Y \end{CD}$$

The inverse is not as easy, because we're given any old morphism $k:
X\to Y = G^M(Y, g: MY\to Y)$ in $C$ and have to make up structure to
form a commutative diagram. But we can do it:

$$(\Phi^M_{X, (Y,g)})^{-1}(k : X\to Y) =
\begin{CD}
MMX @>{\mu_X}>> MX\\
@V{MMk}VV       @V{Mk}VV\\
MMY    @.       MY\\
@V{Mg}VV        @V{g}VV\\
MY @>{g}>>      Y
\end{CD}
$$

So we're just setting $(\Phi^M)^{-1}(k) = g\circ M(k)$. If we insert
$\mu_Y : MMY\to MY$ in the empty space in the middle, we see that the
upper square commutes by naturality, the lower by the fact that $g$ is
an $M$-algebra.

Now I wrote $(\Phi^M)^{-1}$ without checking that this is actually the
inverse of $\Phi^M$. Let's quickly make up for that. Using the
notation of the previous paragraphs,

$$\begin{align*}
(\Phi^M)^{-1}(\Phi^M(h: F^M(X)\to (Y, g))) &= (\Phi^M)^{-1}(h\circ\eta_X) \\
&= g\circ M(h\circ\eta_X) \\
&= h\circ\mu_X\circ M(\eta_X) \\
&= h,
\end{align*}$$

where we used the fact that $h$ is a morphism of $M$-algebras and the
right identity law for monads, and

$$\begin{align*}
\Phi^M((\Phi^M)^{-1}(k: X\to Y)) &= \Phi^M(g\circ M(k))\\
&= g\circ M(k)\circ \eta_X\\
&= g\circ \eta_Y\circ k\\
&= k
\end{align*}$$

by naturality of $\eta$ and the fact that $g$ is an $M$-algebra.

The last thing to check is naturality. In the first variable: Let $f :
T\to X$ be a morphism, then for $h\in\hom_{C^M}(F^MX, (Y,g))$,
$\hom_{C^M}(F^M(f), (Y,g))(h) = h\circ M(f)$, which is sent to $h\circ
M(f)\circ\eta_T = h\circ\eta_X\circ f$ due to naturality, which is
just $\hom_C(f, G^M(Y,g))(\Phi^M(h))$. In the second variable: Let $f
: (Y,g)\to(T,h)$ be a morphism in $C^M$. Then obviously
$\Phi^M(\hom_{C^M}(F^MX, f)(h)) = f\circ h \circ \eta_X = \hom_C(X,
G^M(f))(\Phi^M(h))$ for $h\in\hom_{C^M}(F^MX, (Y,g))$.

# The category of adjunctions that form a given monad

There can be many adjunctions that form a given monad $M$. Let's call
them $M$-adjunctions. To relate them, the elementary idea of category
theory tells us: Look for the morphisms!

Following MacLane, let us denote an $M$-adjunction by a quadruple $(F,
G, \eta, \varepsilon)$, where $F: C\to D$, $G: D\to C$ is an adjoint
pair of functors with $M=GF$, $\eta: \Id\natto GF$ is the unit of the
adjunction and the monad, and $\varepsilon: FG\natto\Id$ is the counit
of the adjunction.[^AdjT_Notation]

[^AdjT_Notation]: You'll notice that $\eta$ is always the same. This
is because MacLane introduces a more general notion morphism of
adjunctions, that need not form the same monad (where $\eta$ can thus
change from object to object):

    $$\begin{CD}
    C_1 @>{F_1}>> D_1 @>{G_1}>> C_1\\
    @V{L}VV   @V{K}VV    @V{L}VV\\
    C_2 @>{F_2}>> D_2 @>{G_2}>> C_2
    \end{CD}$$

    We're using a special case, where $L$ is always the identity.

A morphism of $M$-adjunctions $(F_1, G_1, \eta, \varepsilon_1)\to
(F_2, G_2, \eta, \varepsilon_2)$ is a functor $K: D_1\to D_2$, called
*comparison functor*, such that the following diagram commutes:

$$\begin{CD}
C @>{F_1}>> D_1 @>{G_1}>> C\\
@|          @V{K}VV       @|\\
C @>{F_2}>> D_2 @>{G_2}>> C
\end{CD}$$

that is, we require $F_2=K\circ F_1$ and $G_1 = G_2\circ K$. These
morphisms compose in an obvious way, so we obtain the category of
$M$-adjunctions, $\mathcal A_M$.

The rest of the article will be dedicated to showing the roles of the
Kleisli and the Eilenberg-Moore adjunction in this category.

### Theorem:

Let $(M,\eta,\mu)$ be a monad on a category $C$, and let $\mathcal
A_M$ be the category of $M$-adjunctions.

1) The Kleisli adjunction $(F_M, G_M, \eta, \varepsilon_M)$ is an
initial object in $\mathcal A_M$.

2) The Eilenberg-Moore adjunction $(F^M, G^M, \eta, \varepsilon^M)$ is
a terminal object in $\mathcal A_M$.

#### Proof:

Let $(F, G, \eta, \varepsilon)$ be an $M$-adjunction, given by
$\Phi: \hom_C(FX,Y)\cong\hom_D(X,GY)$.

1. We define a functor $K: C_M\to D$ such that $K\circ F_M = F$: Since
$F_M$ acts as the identity on objects, we have no choice but to set
$K(X) = F(S)$. On morphisms $f: X\to M(Y)$, we set $K(f) =
\varepsilon_{FY}\circ F(f)$.

The identity corresponding to an object $X$ in the Kleisli category is
$\eta_X : X\to_M X$, and $K(\eta_X) = \varepsilon_{FX}\circ F(\eta_X)
= \id_{FX}$ by the triangle equations, so $K$ preserves identities. If
$f: X\to M(Y)$ and $g: Y\to M(Z)$ are Kleisli arrows,

$$\begin{align*}
K(g\circ_M f) &= \varepsilon_{FZ}\circ F(\mu_Z\circ M(g)\circ f)\\
&= \underline{\varepsilon_{FZ}\circ FG\varepsilon_{FZ}}\circ FGFg \circ Ff\\
&= \varepsilon_{FZ}\circ \underline{\varepsilon_{FGFZ}\circ FGFg} \circ Ff\\
&= \varepsilon_{FZ}\circ Fg\circ \varepsilon_{FY}\circ Ff\\
&= K(g) \circ K(f),
\end{align*}$$

by the diagram associated with $\varepsilon\bullet\varepsilon$ and
naturality, so $K$ is indeed a functor.

Now we've already seen $K(F_M(X)) = F()$ for objects $X$, and for
$f: X\to Y$, we have $K(F_M(f)) = K(\eta_X\circ f) =
\varepsilon_{FY}\circ F(\eta_X)\circ F(f) = F(f)$ by the triangle
equality.

Also, $G(K(X)) = G(F(X)) = M(X) = G_M(X)$, and if $f: X\to_M Y$ is a
morphism in $C_M$, $G(K(f)) = G(\varepsilon_{FY}\circ F(f)) =
G(\varepsilon_{FY})\circ M(f) = \mu_Y\circ M(f) = G_M(f)$.

It remains to show that the action of $K$ on morphisms of $C_M$ is
uniquely determined. Let $L$ be another functor $C_M\to D$ such that
$G\circ L = G_M$ and which satisfies $L(X) = F(X)$ on objects. We're
going to use the interplay between $\Phi$, $\eta$ and $\varepsilon$
now. For a $C_M$-morphism $f: X\to_M Y$, we have $G(L(f)) = G(K(f))$,
hence $G(L(f))\circ\eta_X = G(K(f))\circ\eta_X$. We can rewrite both
sides in terms of $\Phi$: $\Phi_{X,FY}(L(f)) = \Phi_{X,FY}(K(f))$,
from which follows $L(f) = K(f)$, because $\Phi_{X,FY}$ is a
bijection. We conclude that $L=K$.

2) We define a functor $K: D\to C^M$ such that $K\circ F = F^M$ and
$G^M\circ K = G$. Since $K(FX) = F^M(X) = (MX, \mu_X) = (GFX,
G(\varepsilon_{FX}))$, an obvious choice is $K(Y) = (GY,
G(\varepsilon_Y))$. This also satisfies $G^M(KY) = GY$.

For a morphism $f:X\to Y$ in $D$, $K(f)$ is a morphism in the
Eilenberg-Moore category between the free $M$-algebras $K(X)$ and
$K(Y)$, but as $G^M$ is a forgetful functor, the condition $G^M(Kf) =
G(f)$ forces $K(f) = G(f)$.

$$\begin{CD}
MG(X)   @>{G(\varepsilon_X)}>>   G(X)\\
@V{MG(f)}VV                    @V{G(f)}VV\\
MG(Y)   @>{G(\varepsilon_Y)}>>   G(Y)
\end{CD}
\quad\leadsto\quad
\begin{CD}
G(X)\\ @V{G(f)}VV \\ G(Y)
\end{CD}$$

The remainder of the proof is dedicated to showing that $K$ is
uniquely determined. It is clear that we had no choice in the
definition of $K(Y)$ for objects $Y$ in the image of $F$, neither did
we have a choice in the definition of $K(f)$. It is not yet clear that
$K(Y)$ must be $(GY, G(\varepsilon_Y))$ in general. This has to do
with the seemingly arbitrary choice of $\mu_X$ as the "free
$M$-algebra" $F^M(X)$. Just because we can't think of anything else
right away doesn't mean it's unique.

We proceed in three steps. First, the following diagram is commutative
for all $X\in C$, $Y\in D$:

$$\begin{CD}
\hom_D(FX, Y) @>{\Phi_{XY}}>> \hom_C(X, GY)\\
@V{K_{FX,Y}}VV                       @|\\
\hom_{C^M}(F^MX, KY)  @>{\Phi^M_{X,KY}}>> \hom_C(X, GY)
\end{CD}$$

Here, $K_{FX,Y}$ denotes the action of $K$ on morphisms,
$\hom_D(FX,Y)\to\hom_{C^M}(KFX, KY),\,f\mapsto K(f)$. Keep in mind
that $KFX = F^MX$ and $G^MKY = GY$.

To see that this is true, realize that $\Phi_{XY}(f) =
G(f)\circ\eta_X$ and $\Phi^M_{X,KY}(K(f)) = G^M(K(f))\circ\eta_X =
G(f)\circ\eta_X$, too.

Second, recall that the counit $\varepsilon$ arises as the image of
the identity under the inverse adjunction. Thus
$\Phi^M_{GY,KY}(K(\varepsilon_Y)) = \Phi_{GY,Y}(\varepsilon_Y) =
\id_{GY} = \id_{G^M(KY)}$, therefore $K(\varepsilon_Y) =
(\Phi^M_{GY,KY})^{-1}(\id_{G^M(KY)}) = \varepsilon^M_{KY}$, for all $Y\in D$.

Third, $\varepsilon^M_{(A,h)} = h$ in general, so the structure
morphism of $K(Y)$ is $\varepsilon^M_{K(Y)} = K(\varepsilon_Y) =
G(\varepsilon_Y)$, for all $Y\in D$.

This concludes the proof.

# Additional notes

* Up to isomorphism of functors, the currying adjunction is the only
  adjunction that stays inside $\cat{Set}$. This seems to mean that
  the `State` monad is the only monad that is formed in this way (up
  to isomorphism.) I'm going to look into this in another article.