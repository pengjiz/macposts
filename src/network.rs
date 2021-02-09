//! Representation of transportation networks.

use std::cmp::max;
use std::fmt;
use std::hash::Hash;

/// Default index type.
pub type DefaultIx = u32;

/// Trait for link and node indices.
pub trait IndexType: Copy + Ord + Hash + fmt::Debug + 'static {
    fn new(x: usize) -> Self;
    fn index(&self) -> usize;
    fn max() -> Self;
}

impl IndexType for usize {
    #[inline(always)]
    fn new(x: usize) -> Self {
        x
    }

    #[inline(always)]
    fn index(&self) -> usize {
        *self
    }

    #[inline(always)]
    fn max() -> Self {
        std::usize::MAX
    }
}

impl IndexType for u32 {
    #[inline(always)]
    fn new(x: usize) -> Self {
        x as u32
    }

    #[inline(always)]
    fn index(&self) -> usize {
        *self as usize
    }

    #[inline(always)]
    fn max() -> Self {
        std::u32::MAX
    }
}

impl IndexType for u16 {
    #[inline(always)]
    fn new(x: usize) -> Self {
        x as u16
    }

    #[inline(always)]
    fn index(&self) -> usize {
        *self as usize
    }

    #[inline(always)]
    fn max() -> Self {
        std::u16::MAX
    }
}

impl IndexType for u8 {
    #[inline(always)]
    fn new(x: usize) -> Self {
        x as u8
    }

    #[inline(always)]
    fn index(&self) -> usize {
        *self as usize
    }

    #[inline(always)]
    fn max() -> Self {
        std::u8::MAX
    }
}

/// Node index.
#[derive(Copy, Clone, PartialEq, PartialOrd, Eq, Ord, Hash)]
pub struct NodeIndex<Ix = DefaultIx>(Ix);

impl<Ix: IndexType> NodeIndex<Ix> {
    #[inline]
    pub fn new(x: usize) -> Self {
        NodeIndex(IndexType::new(x))
    }

    #[inline]
    pub fn index(self) -> usize {
        self.0.index()
    }

    #[inline]
    pub fn max() -> Self {
        NodeIndex(IndexType::max())
    }
}

impl<Ix: IndexType> From<Ix> for NodeIndex<Ix> {
    fn from(x: Ix) -> Self {
        NodeIndex(x)
    }
}

impl<Ix: fmt::Debug> fmt::Debug for NodeIndex<Ix> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "NodeIndex({:?})", self.0)
    }
}

/// Link index.
#[derive(Copy, Clone, PartialEq, PartialOrd, Eq, Ord, Hash)]
pub struct LinkIndex<Ix = DefaultIx>(Ix);

impl<Ix: IndexType> LinkIndex<Ix> {
    #[inline]
    pub fn new(x: usize) -> Self {
        LinkIndex(IndexType::new(x))
    }

    #[inline]
    pub fn index(self) -> usize {
        self.0.index()
    }

    #[inline]
    pub fn max() -> Self {
        LinkIndex(IndexType::max())
    }
}

impl<Ix: IndexType> From<Ix> for LinkIndex<Ix> {
    fn from(x: Ix) -> Self {
        LinkIndex(x)
    }
}

impl<Ix: fmt::Debug> fmt::Debug for LinkIndex<Ix> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "LinkIndex({:?})", self.0)
    }
}

/// Directions on the network.
#[derive(Copy, Clone, Debug)]
#[repr(u8)]
pub enum Direction {
    /// `Incoming` is the direction entering the current link or node.
    Incoming = 0,
    /// `Outgoing` is the direction leaving the current link or node.
    Outgoing = 1,
}

impl Direction {
    /// Return `0` for `Incoming` and `1` for `Outgoing`.
    #[inline]
    pub fn index(&self) -> usize {
        *self as usize
    }
}

const DIRI: usize = 0;
const DIRO: usize = 1;

// TODO: Add more control mechanisms.
/// Control mechanisms at a node.
#[derive(Copy, Clone, Debug)]
pub enum Control {
    /// `None` means no control at all. All vehicles can pass the node.
    None,
}

/// Node attributes.
#[derive(Debug)]
pub struct NodeAttr {
    /// Name of the node.
    name: String,
    /// Control mechanism.
    control: Control,
}

impl NodeAttr {
    /// Create new node attribute data.
    pub fn new(name: &str, control: Control) -> Self {
        NodeAttr {
            name: name.to_string(),
            control: control,
        }
    }
}

impl Clone for NodeAttr {
    fn clone(&self) -> Self {
        NodeAttr {
            name: self.name.clone(),
            control: self.control.clone(),
        }
    }
}

/// Node type.
#[derive(Debug)]
pub struct Node<Ix = DefaultIx> {
    /// Next links in the adjacency lists of both directions.
    next: [LinkIndex<Ix>; 2],
    /// Node attributes.
    attr: NodeAttr,
}

impl<Ix: IndexType> Clone for Node<Ix> {
    fn clone(&self) -> Self {
        Node {
            next: self.next.clone(),
            attr: self.attr.clone(),
        }
    }
}

/// Link attributes.
#[derive(Debug)]
pub struct LinkAttr {
    /// Name of the link.
    name: String,
}

impl LinkAttr {
    /// Create new link attribute data.
    pub fn new(name: &str) -> Self {
        LinkAttr {
            name: name.to_string(),
        }
    }
}

impl Clone for LinkAttr {
    fn clone(&self) -> Self {
        LinkAttr {
            name: self.name.clone(),
        }
    }
}

/// Link type.
#[derive(Debug)]
pub struct Link<Ix = DefaultIx> {
    /// Next links in the adjacency lists of both directions.
    next: [LinkIndex<Ix>; 2],
    /// Start and end nodes.
    node: [NodeIndex<Ix>; 2],
    /// Link attributes.
    attr: LinkAttr,
}

impl<Ix: IndexType> Link<Ix> {
    /// Index of the source node.
    pub fn source(&self) -> NodeIndex<Ix> {
        self.node[0]
    }

    /// Index of the target node.
    pub fn target(&self) -> NodeIndex<Ix> {
        self.node[1]
    }
}

impl<Ix: IndexType> Clone for Link<Ix> {
    fn clone(&self) -> Self {
        Link {
            next: self.next.clone(),
            node: self.node.clone(),
            attr: self.attr.clone(),
        }
    }
}

/// Network type.
pub struct Network<Ix = DefaultIx> {
    nodes: Vec<Node<Ix>>,
    links: Vec<Link<Ix>>,
}

impl<Ix: IndexType> Clone for Network<Ix> {
    fn clone(&self) -> Self {
        Network {
            nodes: self.nodes.clone(),
            links: self.links.clone(),
        }
    }
}

impl Network {
    /// Convenient method to create a new network with the default index type.
    /// To create a new network with different index type use
    /// `Network::with_capacity`.
    pub fn new() -> Self {
        Network {
            nodes: Vec::new(),
            links: Vec::new(),
        }
    }
}

impl<Ix: IndexType> Network<Ix> {
    /// Create a new network with estimated capacity.
    pub fn with_capacity(node_capacity: usize, link_capacity: usize) -> Self {
        Network {
            nodes: Vec::with_capacity(node_capacity),
            links: Vec::with_capacity(link_capacity),
        }
    }

    /// Return number of nodes in the network.
    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }

    /// Return number of links in the network.
    pub fn link_count(&self) -> usize {
        self.links.len()
    }

    /// Add a node to the network.
    pub fn add_node(&mut self, attr: NodeAttr) -> NodeIndex<Ix> {
        let node = Node {
            next: [LinkIndex::max(), LinkIndex::max()],
            attr: attr,
        };
        let index = NodeIndex::new(self.nodes.len());
        // Check for max capacity and panic if out of capacity.
        assert!(index < NodeIndex::max());
        self.nodes.push(node);
        index
    }

    /// Add a link to the network.
    pub fn add_link(
        &mut self,
        source: NodeIndex<Ix>,
        target: NodeIndex<Ix>,
        attr: LinkAttr,
    ) -> LinkIndex<Ix> {
        let index = LinkIndex::new(self.links.len());
        assert!(index < LinkIndex::max());
        let mut link = Link {
            node: [source, target],
            next: [LinkIndex::max(), LinkIndex::max()],
            attr: attr,
        };

        let s = source.index();
        let t = target.index();
        if max(s, t) >= self.nodes.len() {
            panic!("Network:add_link: node indices out of bounds")
        } else if s == t {
            // Loop link
            link.next = self.nodes[s].next;
            self.nodes[s].next[DIRI] = index;
            self.nodes[s].next[DIRO] = index;
        } else {
            // Normal link
            link.next[DIRO] = self.nodes[s].next[DIRO];
            link.next[DIRI] = self.nodes[t].next[DIRI];
            self.nodes[s].next[DIRO] = index;
            self.nodes[t].next[DIRI] = index;
        }

        self.links.push(link);
        index
    }

    /// Get a reference to the node.
    ///
    /// Normally we should work with indices when possible. However, we do need
    /// access to the node occasionally.
    pub fn get_noderef(&self, index: NodeIndex<Ix>) -> Option<&Node<Ix>> {
        self.nodes.get(index.index())
    }

    /// Get a reference to the link.
    ///
    /// Normally we should work with indices when possible. However, we do need
    /// access to the link occasionally.
    pub fn get_linkref(&self, index: LinkIndex<Ix>) -> Option<&Link<Ix>> {
        self.links.get(index.index())
    }

    /// Get an iterator for link indices in the given direction for the node.
    pub fn get_links(&self, start: NodeIndex<Ix>, dir: Direction) -> Links<Ix> {
        Links {
            links: &self.links,
            next: match self.nodes.get(start.index()) {
                None => [LinkIndex::max(), LinkIndex::max()],
                Some(n) => n.next,
            },
            dir: dir,
        }
    }
}

/// Iterator over all links of a node.
pub struct Links<'a, Ix> {
    /// All links in the network.
    links: &'a [Link<Ix>],
    /// Next link to visit.
    next: [LinkIndex<Ix>; 2],
    /// Direction to explore.
    dir: Direction,
}

impl<'a, Ix> Iterator for Links<'a, Ix>
where
    Ix: IndexType,
{
    type Item = LinkIndex<Ix>;

    fn next(&mut self) -> Option<LinkIndex<Ix>> {
        let d = self.dir.index();
        let index = self.next[d];
        let l = index.index();
        if let Some(link) = self.links.get(l) {
            self.next[d] = link.next[d];
            return Some(index);
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;
    use Direction::*;

    #[test]
    fn basics() {
        let mut network = Network::new();
        let nattr = NodeAttr::new("x", Control::None);
        let n1 = network.add_node(nattr.clone());
        let n2 = network.add_node(nattr.clone());
        let n3 = network.add_node(nattr.clone());
        let lattr = LinkAttr::new("y");
        let l12 = network.add_link(n1, n2, lattr.clone());
        let l13 = network.add_link(n1, n3, lattr.clone());
        network.add_link(n1, n1, lattr.clone());
        network.add_link(n1, n2, lattr.clone());

        assert_eq!(network.node_count(), 3);
        assert_eq!(network.link_count(), 4);
        assert_eq!(network.get_linkref(l12).unwrap().source(), n1);
        assert_eq!(network.get_linkref(l13).unwrap().target(), n3);
    }

    #[test]
    fn normal_links() {
        let mut network = Network::new();
        let n1 = network.add_node(NodeAttr::new("1", Control::None));
        let n2 = network.add_node(NodeAttr::new("2", Control::None));
        let n3 = network.add_node(NodeAttr::new("3", Control::None));
        let l12 = network.add_link(n1, n2, LinkAttr::new("12"));
        let l13 = network.add_link(n1, n3, LinkAttr::new("13"));
        let l32 = network.add_link(n3, n2, LinkAttr::new("32"));

        let l1o: HashSet<LinkIndex> = network.get_links(n1, Outgoing).collect();
        assert_eq!(l1o.len(), 2);
        for l in &[l12, l13] {
            assert!(l1o.contains(l));
        }

        let l1i: Vec<LinkIndex> = network.get_links(n1, Incoming).collect();
        assert_eq!(l1i.len(), 0);

        let l2i: HashSet<LinkIndex> = network.get_links(n2, Incoming).collect();
        assert_eq!(l2i.len(), 2);
        for l in &[l12, l32] {
            assert!(l2i.contains(l));
        }
    }

    #[test]
    fn loop_links() {
        let mut network = Network::new();
        let n1 = network.add_node(NodeAttr::new("1", Control::None));
        let n2 = network.add_node(NodeAttr::new("2", Control::None));
        let n3 = network.add_node(NodeAttr::new("3", Control::None));
        let l11 = network.add_link(n1, n1, LinkAttr::new("11"));
        let l12 = network.add_link(n1, n2, LinkAttr::new("12"));
        network.add_link(n2, n2, LinkAttr::new("22"));
        network.add_link(n2, n3, LinkAttr::new("23"));
        network.add_link(n3, n3, LinkAttr::new("33"));
        let l31 = network.add_link(n3, n1, LinkAttr::new("31"));

        let l1o: HashSet<LinkIndex> = network.get_links(n1, Outgoing).collect();
        assert_eq!(l1o.len(), 2);
        for l in &[l12, l11] {
            assert!(l1o.contains(l));
        }
        let l1i: HashSet<LinkIndex> = network.get_links(n1, Incoming).collect();
        assert_eq!(l1i.len(), 2);
        for l in &[l11, l31] {
            assert!(l1i.contains(l));
        }
    }

    #[test]
    fn parallel_links() {
        let mut network = Network::new();
        let n1 = network.add_node(NodeAttr::new("1", Control::None));
        let n2 = network.add_node(NodeAttr::new("2", Control::None));
        let l12a = network.add_link(n1, n2, LinkAttr::new("12a"));
        let l12b = network.add_link(n1, n2, LinkAttr::new("12b"));
        let l12c = network.add_link(n1, n2, LinkAttr::new("12c"));

        let l1o: HashSet<LinkIndex> = network.get_links(n1, Outgoing).collect();
        assert_eq!(l1o.len(), 3);
        let l2i: HashSet<LinkIndex> = network.get_links(n2, Incoming).collect();
        assert_eq!(l2i.len(), 3);
        for l in &[l12a, l12b, l12c] {
            assert!(l1o.contains(l));
            assert!(l2i.contains(l));
        }
    }

}
